/*
** E2K IR assembler (SSA IR -> machine code).
** Copyright (C) 2005-2025 Mike Pall. See Copyright Notice in luajit.h
*/

/* -- Register allocator extensions --------------------------------------- */

static Reg ra_pred(ASMState *as, RegSet allow)
{
  lj_assertA((allow & RSET_PRED) == allow, "RegSet should include only pred");
  Reg r = ra_pick(as, allow);
  ra_modified(as, r);
  RA_DBGX((as, "assign predicate    $r", r));
  return r;
}

static Reg ra_ctpr(ASMState *as, RegSet allow)
{
  lj_assertA((allow & RSET_CTPR) == allow, "RegSet should include only ctpr");
  Reg r = ra_pick(as, allow);
  ra_modified(as, r);
  RA_DBGX((as, "assign ctpr         $r", r));
  return r;
}

static Reg ra_hintalloc(ASMState *as, IRRef ref, Reg hint, RegSet allow)
{
  Reg r = IR(ref)->r;
  if (ra_noreg(r)) {
    if (!ra_hashint(r) && !iscrossref(as, ref))
      ra_sethint(IR(ref)->r, hint);  /* Propagate register hint. */
    r = ra_allocref(as, ref, allow);
  }
  ra_noweak(as, r);
  return r;
}

/* -- Guard handling ------------------------------------------------------ */

/* Setup exit stub after the end of each trace. */
static void asm_exitstub_setup(ASMState *as)
{
  /* Register allocation is not started yet */
  MCode *mxp = as->mctop;
  /* Should be in separate bundle for patchexit */
  emit_ibranch(as, (ptrdiff_t)((void *)lj_vm_exit_handler - (void *)mxp),
               0, 0, &mxp);
  emit_snapno(as, as->T->traceno, &mxp);
  emit_alopf3_ri(as, 0, E2K_STW, RID_SP, SPOFS_TMP, RID_TMP, &mxp);

  as->mctop = mxp;
}

/* Keep this in-sync with exitstub_trace_addr(). */
#define asm_exitstub_addr(as) ((as)->mctop)

/* Emit conditional branch to exit for guard */
static void asm_guard(ASMState *as, Reg pred, int inverted)
{
  MCode *target = asm_exitstub_addr(as);
  MCode *p = as->mcp;
  if (LJ_UNLIKELY(p == as->invmcp)) {
    as->invmcp = NULL;
    as->loopinv = 1;
    as->mcp = p + 4;
    inverted = inverted ? 0 : 1;
    target = p; /* Patch target later in asm_loop_fixup. */
  }
  emit_ibranch(as, (ptrdiff_t)((void *)target - (void *)p),
               pred, inverted, &as->mcp);
  emit_snapno(as, as->snapno, &as->mcp);
}

/* -- Operand fusion ------------------------------------------------------ */

/* Limit linear search to this distance. Avoids O(n^2) behavior. */
#define CONFLICT_SEARCH_LIM 31

/* Check if there's no conflicting instruction between curins and ref. */
static int noconflict(ASMState *as, IRRef ref, IROp conflict)
{
  IRIns *ir = as->ir;
  IRRef i = as->curins;
  if (i > ref + CONFLICT_SEARCH_LIM)
    return 0; /* Give up, ref is too far away. */
  while (--i > ref)
    if (ir[i].o == conflict)
      return 0; /* Conflict found. */
  return 1;  /* Ok, no conflict. */
}

/* Fuse the array base of colocated arrays. */
static int32_t asm_fuseabase(ASMState *as, IRRef ref)
{
  IRIns *ir = IR(ref);
  if (ir->o == IR_TNEW && ir->op1 <= LJ_MAX_COLOSIZE &&
      !neverfuse(as) && noconflict(as, ref, IR_NEWREF))
    return (int32_t)sizeof(GCtab);
  return 0;
}

/* Fuse array/hash/upvalue reference into register+offset operand. */
static Reg asm_fuseahuref(ASMState *as, IRRef ref, int32_t *ofsp, RegSet allow)
{
  IRIns *ir = IR(ref);
  if (ra_noreg(ir->r)) {
    if (ir->o == IR_AREF) {
      if (mayfuse(as, ref)) {
        if (irref_isk(ir->op2)) {
          IRRef tab = IR(ir->op1)->op1;
          int32_t ofs = asm_fuseabase(as, tab);
          IRRef refa = ofs ? tab : ir->op1;
          ofs += 8*IR(ir->op2)->i;
          *ofsp = ofs;
          return ra_alloc1(as, refa, allow);
        }
      }
    } else if (ir->o == IR_HREFK) {
      if (mayfuse(as, ref)) {
        int32_t ofs = (int32_t)(IR(ir->op2)->op2 * sizeof(Node));
        *ofsp = ofs;
        return ra_alloc1(as, ir->op1, allow);
      }
    } else if (ir->o == IR_UREFC) {
      if (irref_isk(ir->op1)) {
        GCfunc *fn = ir_kfunc(IR(ir->op1));
        GCupval *uv = &gcref(fn->l.uvptr[(ir->op2 >> 8)])->uv;
        intptr_t ofs = dispofs(as, &uv->tv);
        *ofsp = ofs;
        return RID_DISPATCH;
      }
    } else if (ir->o == IR_TMPREF) {
      *ofsp = (int32_t)dispofs(as, &J2G(as->J)->tmptv);
      return RID_DISPATCH;
    }
  }
  *ofsp = 0;
  return ra_alloc1(as, ref, allow);
}

/* Fuse XLOAD/XSTORE reference into load/store operand. */
static IRRef asm_fusexref(ASMState *as, IRRef ref, intptr_t *ofs)
{
  IRIns *ir = IR(ref);
  if (ra_noreg(ir->r) && canfuse(as, ir)) {
    if ((ir->o == IR_ADD) && (irref_isk(ir->op2))) {
      *ofs = *ofs + get_kval(as, ir->op2);
      return ir->op1;
    } else if ((ir->o == IR_STRREF) && irref_isk(ir->op2)) {
      *ofs = (intptr_t)sizeof(GCstr) + get_kval(as, ir->op2);
      return ir->op1;
    } else if ((ir->o == IR_STRREF) && irref_isk(ir->op1)) {
      *ofs = (intptr_t)sizeof(GCstr) + get_kval(as, ir->op1);
      return ir->op2;
    }
  }
  return ref;
}

/* -- Calls --------------------------------------------------------------- */

/* Generate a call to a C function. */
static void asm_gencall(ASMState *as, const CCallInfo *ci, IRRef *args)
{
  uint32_t n, nargs = CCI_XNARGS(ci);
  uint32_t is_vararg = ci->flags & CCI_VARARG;
  int32_t ofs = is_vararg ? 0 : STACKARG_OFS;
  Reg gpr = RID_NONE, ctpr = ra_ctpr(as, RSET_CTPR);
  if (ci->func)
    emit_call(as, ctpr, 0, 0, PIPE_WBS, &as->mcp);
  for (gpr = REGARG_FIRSTGPR; gpr <= REGARG_LASTGPR; gpr++)
    as->cost[gpr] = REGCOST(~0u, ASMREF_L);
  gpr = REGARG_FIRSTGPR;

  for (n = 0; n < nargs; n++) { /* Setup args. */
    IRRef ref = args[n];
    if (ref) {
      IRIns *ir = IR(ref);
      if (gpr <= REGARG_LASTGPR) {
        lj_assertA(rset_test(as->freeset, gpr),
                   "arg%d not free", gpr-REGARG_FIRSTGPR); /*  Already evicted. */
        ra_leftov(as, gpr, ref);
        if (is_vararg) {
          emit_spstore(as, ir, gpr, ofs);
          ofs += 8;
        }
        gpr++;
      } else {
        Reg r = ra_alloc1(as, ref, RSET_GPR);
        emit_spstore(as, ir, r, ofs);
        ofs += 8;
      }
    } else {
      if (gpr <= REGARG_LASTGPR) {
        if (is_vararg) ofs += 8;
        gpr++;
      } else {
        ofs += 8;
      }
    }
    checkmclim(as);
  }
  if (ci->func) {
    emit_prepcall(as, ctpr, ci->func, &as->mcp);
  }
}

/* Setup result reg/sp for call. Evict scratch regs. */
static void asm_setupresult(ASMState *as, IRIns *ir, const CCallInfo *ci)
{
  RegSet drop = RSET_SCRATCH;
  int hiop = ((ir+1)->o == IR_HIOP && !irt_isnil((ir+1)->t));

  if (ra_hasreg(ir->r))
    rset_clear(drop, ir->r); /* Dest reg handled below. */
  if (hiop && ra_hasreg((ir+1)->r))
    rset_clear(drop, (ir+1)->r);  /* Dest reg handled below. */
  ra_evictset(as, drop);  /* Evictions must be performed first. */
  if (ra_used(ir)) {
    lj_assertA(!irt_ispri(ir->t), "PRI dest");
    if (hiop) {
      ra_destpair(as, ir);
    } else {
      ra_destreg(as, ir, RID_RET);
    }
  }
}

static void asm_callx(ASMState *as, IRIns *ir)
{
  IRRef args[CCI_NARGS_MAX*2];
  CCallInfo ci;
  IRRef func;
  IRIns *irf;
  Reg ctpr = RID_NONE;
  ci.flags = asm_callx_flags(as, ir);
  asm_collectargs(as, ir, &ci, args);
  asm_setupresult(as, ir, &ci);
  func = ir->op2; irf = IR(func);
  if (irf->o == IR_CARG) { func = irf->op1; irf = IR(func); }
  if (irref_isk(func)) {  /* Call to constant address. */
    ci.func = (ASMFunction)(void *)get_kval(as, func);
  } else {
    ctpr = ra_ctpr(as, RSET_CTPR);
    emit_call(as, ctpr, 0, 0, PIPE_WBS, &as->mcp);
    ci.func = (ASMFunction)(void *)0;
  }
  asm_gencall(as, &ci, args);
  if (!ci.func) {
    Reg r = ra_alloc1(as, func, RSET_GPR & ~RSET_SCRATCH);
    emit_alopf2_r(as, 0, E2K_MOVTD, r, ctpr, &as->mcp);
  }
}

/* -- Returns ------------------------------------------------------------- */

/* Return to lower frame. Guard that it goes to the right spot. */
static void asm_retf(ASMState *as, IRIns *ir)
{
  Reg base = ra_alloc1(as, REF_BASE, RSET_GPR);
  void *pc = ir_kptr(IR(ir->op2));
  int32_t delta = 1+LJ_FR2+bc_a(*((const BCIns *)pc - 1));
  as->topslot -= (BCReg)delta;
  if ((int32_t)as->topslot < 0) as->topslot = 0;
  irt_setmark(IR(REF_BASE)->t);  /* Children must not coalesce with BASE reg. */
  emit_setgl(as, base, jit_base);
  emit_addptr(as, base, -8*delta);
  Reg pred = ra_pred(as, RSET_PRED);
  Reg tmp = ra_scratch(as, rset_exclude(RSET_GPR, base));
  asm_guard(as, pred, 1);
  emit_alopf7_ri(as, 0, E2K_CMPEDB, tmp, (intptr_t)pc, pred, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_LDD, base, LJ_FR2 ? -8 : -4, tmp, &as->mcp);
}

/* -- Buffer operations --------------------------------------------------- */

#if LJ_HASBUFFER
static void asm_bufhdr_write(ASMState *as, Reg sb)
{
  RegSet allow = RSET_GPR;
  Reg tmp1 = ra_scratch(as, rset_clear(allow, sb));
  Reg tmp2 = ra_scratch(as, rset_clear(allow, tmp1));
  IRIns irgc;
  irgc.ot = IRT(0, IRT_PGC);  /* GC type. */
  emit_storeofs(as, &irgc, tmp2, sb, offsetof(SBuf, L));
  emit_alopf1_rr(as, 0, E2K_ORD, tmp2, tmp1, tmp2, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_ANDD, tmp1, SBUF_MASK_FLAG, tmp1, &as->mcp);
  emit_getgl(as, tmp2, cur_L);
  emit_loadofs(as, &irgc, tmp1, sb, offsetof(SBuf, L));
}
#endif

/* -- Type conversions ---------------------------------------------------- */

static void asm_tointg(ASMState *as, IRIns *ir, Reg left)
{
  Reg pred = ra_pred(as, RSET_PRED);
  Reg tmp = ra_scratch(as, rset_exclude(RSET_GPR, left));
  Reg dest = ra_dest(as, ir, RSET_GPR);
  asm_guard(as, pred, 1);
  emit_alopf7_rr(as, 0, E2K_FCMPEQDB, left, tmp, pred, &as->mcp);
  emit_alopf2_r(as, 0, E2K_ISTOFD, dest, tmp, &as->mcp);
  emit_alopf2_r(as, 0, E2K_FDTOISTR, left, dest, &as->mcp);
}

static void asm_tobit(ASMState *as, IRIns *ir)
{
  Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
  Reg right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
  Reg dest = ra_dest(as, ir, RSET_GPR);
  emit_alopf1_rr(as, 0, E2K_FADDD, left, right, dest, &as->mcp);
}

static void asm_conv(ASMState *as, IRIns *ir)
{
  IRType st = (IRType)(ir->op2 & IRCONV_SRCMASK);
  Reg dest = RID_NONE, left = RID_NONE;
  int stfp = (st == IRT_NUM || st == IRT_FLOAT);
  int st64 = (st == IRT_I64 || st == IRT_U64 || st == IRT_P64);
  uint32_t op = 0;
  lj_assertA(irt_type(ir->t) != st, "inconsistent types for CONV");
  if (irt_isfp(ir->t)) {
    dest = ra_dest(as, ir, RSET_GPR);
    if (stfp) { /* FP to FP conversion */
      left = ra_alloc1(as, ir->op1, RSET_GPR);
      op = (st == IRT_NUM) ? E2K_FDTOFS : E2K_FSTOFD;
      emit_alopf2_r(as, 0, op, left, dest, &as->mcp);
    } else if (st == IRT_U32) { /* U32 to FP conversion */
      left = ra_alloc1(as, ir->op1, RSET_GPR);
      op = irt_isnum(ir->t) ? E2K_IDTOFD : E2K_IDTOFS;
      emit_alopf2_r(as, 0, op, dest, dest, &as->mcp);
      emit_alopf1_ir(as, 0, E2K_SXT, SXT_WZ, left, dest, &as->mcp);
    } else if (st == IRT_U64) { /* U64 to FP conversion */
      RegSet allow = RSET_GPR;
      left = ra_alloc1(as, ir->op1, rset_clear(allow, dest));
      Reg tmp1 = ra_scratch(as, rset_clear(allow, left));
      Reg tmp2 = ra_scratch(as, rset_clear(allow, tmp1));
      Reg pred = ra_pred(as, RSET_PRED);
      op = irt_isnum(ir->t) ? E2K_IDTOFD : E2K_IDTOFS;
      emit_mrgc(as, emit_alopf1_rr(as, 1, irt_isnum(ir->t) ? E2K_MERGED : E2K_MERGES,
                                  tmp2, tmp1, dest, 0), pred, 0, &as->mcp);
      emit_alopf1_rr(as, 1, irt_isnum(ir->t) ? E2K_FADDD : E2K_FADDS,
                     tmp1, tmp1, tmp1, &as->mcp);
      emit_alopf2_r(as, 1, op, left, tmp2, &as->mcp);
      emit_alopf7_ri(as, 0, E2K_CMPLDB, left, 0x0, pred, &as->mcp);
      emit_alopf2_r(as, 1, op, tmp1, tmp1, &as->mcp);
      emit_alopf1_rr(as, 1, E2K_ORD, tmp2, tmp1, tmp1, &as->mcp);
      emit_alopf1_ri(as, 1, E2K_SHRD, left, 0x1, tmp2, 0);
      emit_alopf1_ri(as, 1, E2K_ANDD, left, 0x1, tmp1, &as->mcp);
    } else {
      left = ra_alloc1(as, ir->op1, RSET_GPR);
      op = irt_isnum(ir->t) ? (st64 ? E2K_IDTOFD : E2K_ISTOFD) :
                              (st64 ? E2K_IDTOFS : E2K_ISTOFS);
      emit_alopf2_r(as, 0, op, left, dest, &as->mcp);
    }
  } else if (stfp) { /* FP to INT conversion */
    left = ra_alloc1(as, ir->op1, RSET_GPR);
    if (irt_isguard(ir->t)) {
      /* Checked conversions are only supported from NUM to INT */
      lj_assertA(irt_isint(ir->t) && st == IRT_NUM,
                 "bad type for checked CONV");
      asm_tointg(as, ir, left);
    } else {
      dest = ra_dest(as, ir, RSET_GPR);
      Reg tmp = ra_scratch(as, rset_exclude(RSET_GPR, left));
      Reg pred = ra_pred(as, RSET_PRED);
      if (irt_isu64(ir->t)) { /* FP to U64 */
        intptr_t k = (st == IRT_NUM) ? 0x43e0000000000000 : 0x5f000000;
        op = (st == IRT_NUM) ? E2K_FDTOIDTR : E2K_FSTOIDTR;
        emit_rlp(as, emit_alopf1_ri(as, 1, E2K_ADDD, tmp, 0x8000000000000000,
                                    dest, 0), pred, 1, 0);
        emit_rlp(as, emit_alopf2_r(as, 0, op, left, dest, 0), pred, 0, &as->mcp);
        emit_alopf2_r(as, 1, op, tmp, tmp, &as->mcp);
        emit_alopf7_ri(as, 0, (st == IRT_NUM) ? E2K_FCMPLTDB : E2K_FCMPLTSB,
                       left, k, pred, 0);
        emit_alopf1_ri(as, 1, (st == IRT_NUM) ? E2K_FSUBD : E2K_FSUBS,
                       left, k, tmp, &as->mcp);
      } else if (irt_isu32(ir->t)) { /* FP to U32 */
        op = (st == IRT_NUM) ? E2K_FDTOIDTR : E2K_FSTOIDTR;
        emit_alopf1_ri(as, 0, E2K_GETFD, dest, 0x800, dest, &as->mcp);
        emit_alopf2_r(as, 0, op, left, dest, &as->mcp);
      } else {
        op = irt_is64(ir->t) ?
             (st == IRT_NUM ? E2K_FDTOIDTR : E2K_FSTOIDTR) :
             (st == IRT_NUM ? E2K_FDTOISTR : E2K_FSTOISTR);
        emit_alopf2_r(as, 0, op, left, dest, &as->mcp);
      }
    }
  } else { /* INT to INT conversion */
    dest = ra_dest(as, ir, RSET_GPR);
    if (st >= IRT_I8 && st <= IRT_U16) { /* Extend to 32/64 bit integer. */
      left = ra_alloc1(as, ir->op1, RSET_GPR);
      emit_alopf1_ir(as, 0, E2K_SXT,
                     (ir->op2 & IRCONV_SEXT) ?
                     (st == IRT_I8 ? SXT_BS : SXT_HS) :
                     (st == IRT_U8 ? SXT_BZ : SXT_HZ), left, dest, &as->mcp);
    } else { /* 32/64 bit integer conversions */
      if (irt_is64(ir->t)) {
        if (st64) { /* 64/64 bit no-op (cast) */
          ra_leftov(as, dest, ir->op1);
        } else {
          left = ra_alloc1(as, ir->op1, RSET_GPR);
          emit_alopf1_ir(as, 0, E2K_SXT, (ir->op2 & IRCONV_SEXT) ?
                                         SXT_WS : SXT_WZ, left, dest, &as->mcp);
        }
      } else {
        if (st64 && !(ir->op2 & IRCONV_NONE)) {
        /* This is either a 32 bit reg/reg mov which zeroes the hiword
           or a load of the loword from a 64 bit address. */
          left = ra_alloc1(as, ir->op1, RSET_GPR);
          emit_alopf1_ir(as, 0, E2K_SXT, SXT_WZ, left, dest, &as->mcp);
        } else { /* 32/32 bit no-op (cast). */
          ra_leftov(as, dest, ir->op1);
        }
      }
    }
  }
}

static void asm_strto(ASMState *as, IRIns *ir)
{
  const CCallInfo *ci = &lj_ir_callinfo[IRCALL_lj_strscan_num];
  IRRef args[2];
  int32_t ofs = 0;
  RegSet drop = RSET_SCRATCH;
  Reg pred = ra_pred(as, RSET_PRED);
  if (ra_hasreg(ir->r)) rset_set(drop, ir->r);  /* Spill dest reg (if any). */
  ra_evictset(as, drop);
  ofs = sps_scale(ir->s);
  asm_guard(as, pred, 0); /* Test return status. */
  emit_alopf7_ri(as, 0, E2K_CMPEDB, RID_RET, 0, pred, &as->mcp);
  args[0] = ir->op1;      /* GCstr *str */
  args[1] = ASMREF_TMP1;  /* TValue *n  */
  asm_gencall(as, ci, args);
  /* Store the result to the spill slot or temp slots. */
  emit_alopf1_ri(as, 0, E2K_ADDD, RID_SP, ofs,
                 ra_releasetmp(as, ASMREF_TMP1), &as->mcp);
}

/* -- Memory references --------------------------------------------------- */

/* Store tagged value for ref at base+ofs. */
static void asm_tvstore64(ASMState *as, Reg base, int32_t ofs, IRRef ref)
{
  RegSet allow = rset_exclude(RSET_GPR, base);
  IRIns *ir = IR(ref);
  lj_assertA(irt_ispri(ir->t) || irt_isaddr(ir->t) || irt_isinteger(ir->t),
             "store of IR type %d", irt_type(ir->t));
  if (irref_isk(ref)) {
    TValue k;
    lj_ir_kvalue(as->J->L, &k, ir);
    Reg tmp = ra_allock(as, (int64_t)k.u64, allow);
    emit_alopf3_ri(as, 0, E2K_STD, base, ofs, tmp, &as->mcp);
  } else {
    Reg src = ra_alloc1(as, ref, allow);
    allow = rset_exclude(allow, src);
    intptr_t type = (intptr_t)irt_toitype(ir->t) << 47;
    Reg tmp = ra_scratch(as, allow);
    emit_alopf3_ri(as, 0, E2K_STD, base, ofs, tmp, &as->mcp);
    if (irt_isinteger(ir->t)) {
      emit_alopf1_ri(as, 0, E2K_ADDD, tmp, type, tmp, &as->mcp);
      emit_alopf1_ir(as, 0, E2K_SXT, SXT_WZ, src, tmp, &as->mcp);
    } else {
      emit_alopf1_ri(as, 0, E2K_ADDD, src, type, tmp, &as->mcp);
    }
  }
}

/* Get pointer to TValue. */
static void asm_tvptr(ASMState *as, Reg dest, IRRef ref, MSize mode)
{
  if ((mode & IRTMPREF_IN1)) {
    IRIns *ir = IR(ref);
    if (irt_isnum(ir->t)) {
      if (irref_isk(ref) && !(mode & IRTMPREF_OUT1)) {
        /* Use the number constant itself as a TValue. */
        emit_loada(as, dest, ir_knum(ir));
        return;
      }
      Reg src = ra_alloc1(as, ref, RSET_GPR);
      emit_alopf3_ri(as, 0, E2K_STD, dest, 0, src, &as->mcp);
    } else {
      /* Otherwise use g->tmptv to hold the TValue. */
      asm_tvstore64(as, dest, 0, ref);
    }
  }
  emit_loada(as, dest, &J2G(as->J)->tmptv);
}

static void asm_aref(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_GPR;
  Reg dest = ra_dest(as, ir, allow);
  Reg idx, base, tmp;
  if (irref_isk(ir->op2)) {
    IRRef tab = IR(ir->op1)->op1;
    int32_t ofs = asm_fuseabase(as, tab);
    IRRef refa = ofs ? tab : ir->op1;
    ofs += 8*IR(ir->op2)->i;
    base = ra_alloc1(as, refa, allow);
    emit_alopf1_ri(as, 0, E2K_ADDD, base, ofs, dest, &as->mcp);
  } else {
    base = ra_alloc1(as, ir->op1, allow);
    allow = rset_exclude(allow, base);
    idx = ra_alloc1(as, ir->op2, allow);
    allow = rset_exclude(allow, idx);
    tmp = ra_scratch(as, allow);
    emit_alopf1_rr(as, 0, E2K_ADDD, base, tmp, dest, &as->mcp);
    emit_alopf1_ri(as, 0, E2K_SHLD, idx, 3, tmp, &as->mcp);
    /* if its integer extend first */
    if (irt_isinteger(IR(ir->op2)->t)) {
      emit_alopf1_ir(as, 0, E2K_SXT, SXT_WS, idx, idx, &as->mcp);
    }
  }
}

/* Inlined hash lookup. Specialized for key type and for const keys.
** The equivalent C code is:
**   Node *n = hashkey(t, key);
**   do {
**     if (lj_obj_equal(&n->key, key)) return &n->val;
**   } while ((n = nextnode(n)));
**   return niltv(L);
*/
static void asm_href(ASMState *as, IRIns *ir, IROp merge)
{
  RegSet allow = RSET_GPR;
  int destused = ra_used(ir);
  Reg dest = ra_dest(as, ir, allow);
  Reg tab = ra_alloc1(as, ir->op1, rset_clear(allow, dest));
  Reg key = RID_NONE;
  Reg pred3 = RID_PRED3, pred2 = RID_PRED2, pred1 = RID_PRED1;
  Reg tmp1 = ra_scratch(as, rset_clear(allow, tab));
  Reg tmp2 = ra_scratch(as, rset_clear(allow, tmp1));
  Reg tmp3 = ra_scratch(as, rset_clear(allow, tmp2));
  Reg ctpr = ra_ctpr(as, RSET_CTPR);
  IRRef refkey = ir->op2;
  IRIns *irkey = IR(refkey);
  int isk = irref_isk(ir->op2);
  IRType1 kt = irkey->t;
  uint32_t khash;
  MCLabel l_end, l_next, l_exit;
  if (!isk || irt_isnum(kt)) {
    key = ra_alloc1(as, refkey, rset_clear(allow, tmp3));
  }

  /* Key not found in chain: jump to exit (if merged or load niltv. */
  l_end = emit_label(as);
  l_exit = asm_exitstub_addr(as);
  if (merge == IR_NE) {
    /* unconditional asm_guard */
    emit_ibranch(as, (ptrdiff_t)((void *)l_exit - (void *)as->mcp),
                 0, 0, &as->mcp);
    emit_snapno(as, as->snapno, &as->mcp);
  } else if (destused) {
    emit_loada(as, dest, niltvg(J2G(as->J)));
  }

  /* Follow hash chain until the end. */
  emit_ct(as, ctpr, pred3, 1, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_ADDD, tmp3, 0, dest, &as->mcp);
  l_next = emit_label(as);

  /* Type  and value comparison. */
  if (merge == IR_EQ) l_end = l_exit;
  emit_ibranch(as, (ptrdiff_t)((void *)l_end - (void *)as->mcp),
               pred2, 0, &as->mcp);
  if (merge == IR_EQ) {
    emit_snapno(as, as->snapno, &as->mcp);
  }

  if (irt_isnum(kt)) {
    emit_ibranch(as, (ptrdiff_t)((void *)l_next - (void *)as->mcp),
                 pred1, 1, &as->mcp);
    emit_alopf7_ri(as, 0, E2K_CMPBSB, tmp2, (int32_t)LJ_TISNUM, pred1, 0);
    emit_alopf7_ri(as, 1, E2K_CMPEDB, tmp3, 0, pred3, &as->mcp);
    emit_alopf7_rr(as, 0, E2K_FCMPEQDB, tmp1, key, pred2, 0);
    emit_alopf1_ri(as, 0, E2K_SARD, tmp1, 47, tmp2, &as->mcp);
  } else {
    if (isk) {
      intptr_t k = 0;
      if (irt_isaddr(kt)) {
        k = (intptr_t)irt_toitype(kt) << 47 | irkey[1].tv.u64;
      } else {
        lj_assertA(irt_ispri(kt) && !irt_isnil(kt), "bad HREF key type");
        k = ~((intptr_t)~irt_toitype(kt) << 47);
      }
      emit_alopf7_ri(as, 0, E2K_CMPEDB, tmp1, k, pred2, 0);
    } else {
      emit_alopf7_rr(as, 0, E2K_CMPEDB, tmp1, tmp2, pred2, 0);
    }
    emit_alopf7_ri(as, 1, E2K_CMPEDB, tmp3, 0, pred3, &as->mcp);
  }
  emit_alopf1_ri(as, 0, E2K_LDD, dest, (intptr_t)offsetof(Node, key.u64), tmp1, 0);
  emit_alopf1_ri(as, 1, E2K_LDD, dest, (intptr_t)offsetof(Node, next), tmp3, 0);
  emit_copf2(as, E2K_DISP, ctpr, -24 /* HS+CS0+ALS+ALS+LTS+ALIGN */, &as->mcp);
  if (!isk && irt_isaddr(kt)) {
    emit_alopf1_ri(as, 0, E2K_ADDD, key, (intptr_t)irt_toitype(kt) << 47,
                   tmp2, 0);
  }

  /* Load main position relative to tab->node into dest. */
  khash = isk ? ir_khash(as, irkey) : 1;
  if (khash == 0) {
    emit_alopf1_ri(as, 0, E2K_LDD, tab, (intptr_t)offsetof(GCtab, node),
                   dest, &as->mcp);
  } else {
    emit_alopf1_rr(as, 0, E2K_ADDD, dest, tmp1, dest, &as->mcp);
    emit_alopf1_ir(as, 0, E2K_SXT, SXT_WS, tmp1, tmp1, &as->mcp);
    lj_assertA(sizeof(Node) == 24, "bad Node size");
    emit_alopf1_rr(as, 0, E2K_SUBS, tmp2, tmp1, tmp1, &as->mcp);
    emit_alopf1_ri(as, 0, E2K_SHLS, tmp1, 3, tmp1, 0);
    emit_alopf1_ri(as, 0, E2K_SHLS, tmp1, 5, tmp2, &as->mcp);
    if (isk) {
      emit_alopf1_ri(as, 0, E2K_ANDS, tmp2, khash, tmp1, &as->mcp);
    } else {
      emit_alopf1_rr(as, 0, E2K_ANDS, tmp2, tmp1, tmp1, &as->mcp);
    }
    emit_alopf1_ri(as, 0, E2K_LDD, tab, (intptr_t)offsetof(GCtab, node),
                   dest, 0);
    emit_alopf1_ri(as, 0, E2K_LDW, tab, (intptr_t)offsetof(GCtab, hmask),
                   tmp2, 0);
    if (isk) {
      /* Nothing to do */
      as->mcp = emit_bundle_finalize(as, as->mcp);
    } else if (irt_isstr(kt)) {
      emit_alopf1_ri(as, 0, E2K_LDW, key, (intptr_t)offsetof(GCstr, sid),
                     tmp1, &as->mcp);
    } else { /*  Must match with hash*() in lj_tab.c. */
      emit_alopf1_rr(as, 0, E2K_SUBS, tmp1, tmp2, tmp1, &as->mcp);
      emit_alopf1_ri(as, 0, E2K_SCLS, tmp2, HASH_ROT3, tmp2, 0);
      emit_alopf1_rr(as, 0, E2K_XORS, tmp1, tmp2, tmp1, &as->mcp);
      emit_alopf1_ri(as, 0, E2K_SCLS, tmp1, HASH_ROT2, tmp1, 0);
      emit_alopf1_rr(as, 0, E2K_SUBS, tmp2, dest, tmp2, &as->mcp);
      emit_alopf1_rr(as, 0, E2K_XORS, tmp2, tmp1, tmp2, 0);
      emit_alopf1_ri(as, 0, E2K_SCLS, tmp1, HASH_ROT1, dest, &as->mcp);
      if (irt_isnum(kt)) {
        emit_alopf1_rr(as, 0, E2K_ADDS, tmp1, tmp1, tmp1, &as->mcp);
        emit_alopf1_ri(as, 0, E2K_SHRD, key, 32, tmp1, 0);
        emit_alopf1_ri(as, 0, E2K_ADDS, key, 0, tmp2, &as->mcp);
      } else {
        emit_alopf1_ri(as, 0, E2K_SHRD, tmp1, 32, tmp1, &as->mcp);
        emit_alopf1_ri(as, 0, E2K_ADDS, key, 0, tmp2, 0);
        emit_alopf1_ri(as, 0, E2K_ADDD, key, (intptr_t)irt_toitype(kt) << 47,
                       tmp1, &as->mcp);
      }
    }
  }
}

static void asm_hrefk(ASMState *as, IRIns *ir)
{
  IRIns *kslot = IR(ir->op2);
  IRIns *irkey = IR(kslot->op1);
  int32_t ofs = (int32_t)(kslot->op2 * sizeof(Node));
  int32_t kofs = ofs + (int32_t)offsetof(Node, key);
  intptr_t k = 0;
  RegSet allow = RSET_GPR;
  Reg dest = ra_used(ir) ? ra_dest(as, ir, allow) : RID_NONE;
  allow = rset_exclude(allow, dest);
  Reg node = ra_alloc1(as, ir->op1, RSET_GPR);
  allow = rset_exclude(allow, node);
  Reg key = ra_scratch(as, allow);
  lj_assertA(ofs % sizeof(Node) == 0, "unaligned HREFK slot");
  if (irt_ispri(irkey->t)) {
    lj_assertA(!irt_isnil(irkey->t), "bad HREFK key type");
    k = ~((int64_t)~irt_toitype(irkey->t) << 47);
  } else if (irt_isnum(irkey->t)) {
    k = (int64_t)ir_knum(irkey)->u64;
  } else {
    k = ((int64_t)irt_toitype(irkey->t) << 47) | (int64_t)ir_kgc(irkey);
  }
  Reg pred = ra_pred(as, RSET_PRED);
  if (ra_hasreg(dest)) {
    emit_alopf1_ri(as, 0, E2K_ADDD, node, ofs, dest, &as->mcp);
  }
  asm_guard(as, pred, 1);
  emit_alopf7_ri(as, 0, E2K_CMPEDB, key, k, pred, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_LDD, node, kofs, key, &as->mcp);
}

static void asm_uref(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg tmp = RID_NONE;
  int guarded = (irt_t(ir->t) & (IRT_GUARD|IRT_TYPE)) == (IRT_GUARD|IRT_PGC);
  intptr_t ofs = 0;
  if (irref_isk(ir->op1) && !guarded) {
    GCfunc *fn = ir_kfunc(IR(ir->op1));
    MRef *v = &gcref(fn->l.uvptr[(ir->op2 >> 8)])->uv.v;
    ofs = dispofs(as, v);
    emit_alopf1_ri(as, 0, E2K_LDD, RID_DISPATCH, ofs, dest, &as->mcp);
  } else {
    if (guarded) {
      Reg pred = ra_pred(as, RSET_PRED);
      tmp = ra_scratch(as, rset_exclude(RSET_GPR, dest));
      asm_guard(as, pred, ir->o == IR_UREFC ? 0 : 1);
      emit_alopf7_ri(as, 0, E2K_CMPEDB, tmp, 0, pred, &as->mcp);
    }
    ofs = ir->o == IR_UREFC ? (intptr_t)offsetof(GCupval, tv)
                             : (intptr_t)offsetof(GCupval, v);
    int op = ir->o == IR_UREFC ? E2K_ADDD : E2K_LDD;
    emit_alopf1_ri(as, 0, op, dest, ofs, dest, 0);
    if (guarded) {
      ofs = (intptr_t)offsetof(GCupval, closed);
      emit_alopf1_ri(as, 0, E2K_LDB, dest, ofs, tmp, 0);
    }
    as->mcp = emit_bundle_finalize(as, as->mcp);
    if (irref_isk(ir->op1)) {
      GCfunc *fn = ir_kfunc(IR(ir->op1));
      GCobj *o = gcref(fn->l.uvptr[(ir->op2 >> 8)]);
      emit_loada(as, dest, o);
    } else {
      ofs = (intptr_t)offsetof(GCfuncL, uvptr) +
            (intptr_t)sizeof(MRef) * (intptr_t)(ir->op2 >> 8);
      emit_alopf1_ri(as, 0, E2K_LDD, ra_alloc1(as, ir->op1, RSET_GPR),
                     ofs, dest, &as->mcp);
    }
  }
}

static void asm_fref(ASMState *as, IRIns *ir)
{
  UNUSED(as); UNUSED(ir);
  lj_assertA(!ra_used(ir), "unfused FREF");
}

static void asm_strref(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_GPR;
  Reg dest = ra_dest(as, ir, allow);
  Reg base = ra_alloc1(as, ir->op1, rset_clear(allow, dest));
  IRIns *irr = IR(ir->op2);
  int32_t ofs = sizeof(GCstr);
  if (irref_isk(ir->op2)) {
    emit_alopf1_ri(as, 0, E2K_ADDD, base, (intptr_t)(ofs + irr->i),
                   dest, &as->mcp);
  } else {
    /* base + ofs + right(32-bit) */
    Reg right = ra_alloc1(as, ir->op2, rset_clear(allow, base));
    emit_alopf1_rr(as, 0, E2K_ADDD, dest, right, dest, &as->mcp);
    emit_alopf1_ir(as, 0, E2K_SXT, SXT_WS, right, right, 0);
    emit_alopf1_ri(as, 0, E2K_ADDD, base, ofs, dest, &as->mcp);
  }
}

/* -- Loads and stores ---------------------------------------------------- */

static uint32_t asm_loadins(ASMState *as, IRIns *ir, Reg dest)
{
  uint32_t sxt_cop = 0, need_sxt = 0, op = 0;
  switch (irt_type(ir->t)) {
  case IRT_I8:
    need_sxt = 1;
    sxt_cop = SXT_BS;
  case IRT_U8:
    op = E2K_LDB;
    break;
  case IRT_I16:
    need_sxt = 1;
    sxt_cop = SXT_HS;
  case IRT_U16:
    op = E2K_LDH;
    break;
  default:
    op = irt_is64(ir->t) ? E2K_LDD : E2K_LDW;
    break;
  }
  /* ldb and ldh unsigned, need sign extension */
  if (need_sxt) {
    emit_alopf1_ir(as, 0, E2K_SXT, sxt_cop, dest, dest, &as->mcp);
  }
  return op;
}

static uint32_t asm_storeins(ASMState *as, IRIns *ir)
{
  UNUSED(as);
  switch (irt_type(ir->t)) {
  case IRT_I8: case IRT_U8: return E2K_STB;
  case IRT_I16: case IRT_U16: return E2K_STH;
  default:
    if (irt_is64(ir->t)) return E2K_STD;
    else return E2K_STW;
  }
}

static void asm_fload(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg base = RID_NONE;
  uint32_t op = asm_loadins(as, ir, dest);
  int32_t ofs = 0;
  if (ir->op1 == REF_NIL) { /* FLOAD from GG_State with offset. */
    ofs = (int32_t)(ir->op2 << 2) - GG_OFS(dispatch);
    base = RID_DISPATCH;
  } else if (irref_isk(ir->op1)) {
    IRIns *op1 = IR(ir->op1);
    if (op1->o == IR_KPTR || op1->o == IR_KKPTR) {
      ofs = field_ofs[ir->op2] + dispofs(as, ir_kptr(op1));
      base = RID_DISPATCH;
    } else {
      ofs = field_ofs[ir->op2];
      base = ra_alloc1(as, ir->op1, RSET_GPR);
    }
  } else {
    ofs = field_ofs[ir->op2];
    base = ra_alloc1(as, ir->op1, RSET_GPR);
  }
  emit_alopf1_ri(as, 0, op, base, ofs, dest, &as->mcp);
}

static void asm_fstore(ASMState *as, IRIns *ir)
{
  if (ir->r != RID_SINK) {
    Reg src = ra_alloc1(as, ir->op2, RSET_GPR);
    IRIns *irf = IR(ir->op1);
    Reg base = ra_alloc1(as, irf->op1, rset_exclude(RSET_GPR, src));
    int32_t ofs = field_ofs[irf->op2];
    lj_assertA(!irt_isfp(ir->t), "bad FP FSTORE");
    emit_alopf3_ri(as, 0, asm_storeins(as, ir), base, ofs, src, &as->mcp);
  }
}

static void asm_xload(ASMState *as, IRIns *ir)
{
  intptr_t ofs = 0;
  Reg dest = ra_dest(as, ir, RSET_GPR);
  IRRef ref = asm_fusexref(as, ir->op1, &ofs);
  Reg base = ra_alloc1(as, ref, RSET_GPR);
  emit_alopf1_ri(as, 0, asm_loadins(as, ir, dest), base, ofs, dest, &as->mcp);
  if (!irt_is64(IR(ref)->t))
    emit_alopf1_ir(as, 0, E2K_SXT, SXT_WS, base, base, &as->mcp);
}

static void asm_xstore(ASMState *as, IRIns *ir)
{
  if (ir->r != RID_SINK) {
    intptr_t ofs = 0;
    Reg src = ra_alloc1(as, ir->op2, RSET_GPR);
    IRRef ref = asm_fusexref(as, ir->op1, &ofs);
    Reg base = ra_alloc1(as, ref, rset_exclude(RSET_GPR, src));
    emit_alopf3_ri(as, 0, asm_storeins(as, ir), base, ofs, src, &as->mcp);
    if (!irt_is64(IR(ref)->t))
      emit_alopf1_ir(as, 0, E2K_SXT, SXT_WS, base, base, &as->mcp);
  }
}

static void asm_ahuvload(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_GPR;
  Reg base, dest = RID_NONE, type = RID_NONE;
  Reg pred = ra_pred(as, RSET_PRED);
  IRType1 t = ir->t;
  int32_t ofs = 0;
  lj_assertA(irt_isnum(t) || irt_ispri(t) || irt_isaddr(t) ||
             irt_isint(t), "bad load type %d", irt_type(t));
  if (ra_used(ir)) {
    dest = ra_dest(as, ir, allow);
    allow = rset_exclude(allow, dest);
    if (irt_isaddr(t)) {
      emit_alopf1_ri(as, 0, E2K_GETFD, dest, 0xbc0, dest, &as->mcp);
    } else if (irt_isint(t)) {
      emit_alopf1_ir(as, 0, E2K_SXT, SXT_WZ, dest, dest, &as->mcp);
    }
  }
  base = asm_fuseahuref(as, ir->op1, &ofs, allow);
  allow = rset_exclude(allow, base);
  if (ir->o == IR_VLOAD) ofs += 8 * ir->op2;
  type = ra_scratch(as, allow);
  intptr_t k = irt_isnum(t) ? (int32_t)LJ_TISNUM :
               (int32_t)irt_toitype(t);
  asm_guard(as, pred, 1);
  emit_alopf7_ri(as, 0, irt_isnum(t) ? E2K_CMPBSB : E2K_CMPESB,
                 type, k, pred, &as->mcp);
  if (!ra_hasreg(dest)) dest = type;
  emit_alopf1_ri(as, 0, E2K_SARD, dest, 47, type, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_LDD, base, ofs, dest, &as->mcp);
}

static void asm_ahustore(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_GPR;
  Reg base, src = RID_NONE;
  intptr_t type = 0;
  int32_t ofs = 0;
  if (ir->r == RID_SINK)
    return;
  if (irt_isnum(ir->t)) {
    src = ra_alloc1(as, ir->op2, allow);
    allow = rset_exclude(allow, src);
    base = asm_fuseahuref(as, ir->op1, &ofs, allow);
    emit_alopf3_ri(as, 0, E2K_STD, base, ofs, src, &as->mcp);
  } else {
    Reg tmp = RID_NONE;
    if (irt_ispri(ir->t)) {
      tmp = ra_allock(as, ~((int64_t)~irt_toitype(ir->t) << 47), allow);
      allow = rset_exclude(allow, tmp);
    } else {
      tmp = ra_scratch(as, allow);
      allow = rset_exclude(allow, tmp);
      src = ra_alloc1(as, ir->op2, allow);
      allow = rset_exclude(allow, src);
      type = (intptr_t)irt_toitype(ir->t) << 47;
    }
    base = asm_fuseahuref(as, ir->op1, &ofs, allow);
    emit_alopf3_ri(as, 0, E2K_STD, base, ofs, tmp, &as->mcp);
    if (ra_hasreg(src)) {
      if (irt_isinteger(ir->t)) {
        emit_alopf1_ri(as, 0, E2K_ADDD, tmp, type, tmp, &as->mcp);
        emit_alopf1_ir(as, 0, E2K_SXT, SXT_WZ, src, tmp, &as->mcp);
      } else {
        emit_alopf1_ri(as, 0, E2K_ADDD, src, type, tmp, &as->mcp);
      }
    }
  }
}

static void asm_sload(ASMState *as, IRIns *ir)
{
  Reg dest = RID_NONE, base;
  RegSet allow = RSET_GPR;
  IRType1 t = ir->t;
  int32_t ofs = 8*((int32_t)ir->op1-2);
  int op = 0;
  lj_assertA(!(ir->op2 & IRSLOAD_PARENT),
             "bad parent SLOAD");  /* Handled by asm_head_side(). */
  lj_assertA(irt_isguard(ir->t) || !(ir->op2 & IRSLOAD_TYPECHECK),
             "inconsistent SLOAD variant");
  if ((ir->op2 & IRSLOAD_CONVERT) && irt_isguard(t) && irt_isint(t)) {
    dest = ra_scratch(as, allow);
    allow = rset_clear(allow, dest);
    asm_tointg(as, ir, dest);
    t.irt = IRT_NUM; /* Continue with a regular number type check. */
  } else if (ra_used(ir)) {
    lj_assertA(irt_isnum(ir->t) || irt_isint(ir->t) || irt_isaddr(ir->t),
               "bad SLOAD type %d", irt_type(t));
    dest = ra_dest(as, ir, allow);
    allow = rset_clear(allow, dest);
    if (ir->op2 & IRSLOAD_CONVERT) {
      emit_alopf2_r(as, 0, irt_isint(t) ? E2K_FDTOISTR : E2K_ISTOFD,
                    dest, dest, &as->mcp);
      t.irt = irt_isint(t) ? IRT_NUM : IRT_INT;
    } else if (irt_isaddr(t)) {
      /* Clear type from pointers. */
      emit_alopf1_ri(as, 0, E2K_GETFD, dest, 0xbc0, dest, &as->mcp);
    } else if (irt_isint(t) && (ir->op2 & IRSLOAD_TYPECHECK)) {
      /* Sign-extend integers. */
      emit_alopf1_ir(as, 0, E2K_SXT, SXT_WS, dest, dest, &as->mcp);
    }
  }
  base = ra_alloc1(as, REF_BASE, allow);
  if (ir->op2 & IRSLOAD_TYPECHECK) {
    Reg pred = ra_pred(as, RSET_PRED);
    Reg type = ra_scratch(as, rset_clear(allow, base));
    if (!ra_hasreg(dest))
      dest = type;
    if (irt_ispri(t)) {
      asm_guard(as, pred, 1);
      intptr_t k = ~((int64_t)~irt_toitype(t) << 47);
      emit_alopf7_ri(as, 0, E2K_CMPEDB, type, k, pred, &as->mcp);
    } else if (ir->op2 & IRSLOAD_KEYINDEX) {
      asm_guard(as, pred, 1);
      intptr_t k = (int32_t)LJ_KEYINDEX;
      emit_alopf7_ri(as, 0, E2K_CMPESB, type, k, pred, &as->mcp);
      emit_alopf1_ri(as, 0, E2K_SHRD, dest, 32, type, &as->mcp);
    } else {
      intptr_t k = irt_isnum(t) ? (int32_t)LJ_TISNUM :
                   (int32_t)irt_toitype(t);
      asm_guard(as, pred, 1);
      emit_alopf7_ri(as, 0, irt_isnum(t) ? E2K_CMPBSB : E2K_CMPESB,
                     type, k, pred, &as->mcp);
      emit_alopf1_ri(as, 0, E2K_SARD, dest, 47, type, &as->mcp);
    }
    op = E2K_LDD;
  } else {
    op = irt_isint(t) ? E2K_LDW : E2K_LDD;
  }
  emit_alopf1_ri(as, 0, op, base, ofs, dest, &as->mcp);
}

/* -- Allocations --------------------------------------------------------- */
#if LJ_HASFFI
static void asm_cnew(ASMState *as, IRIns *ir)
{
  CTState *cts = ctype_ctsG(J2G(as->J));
  CTypeID id = (CTypeID)IR(ir->op1)->i;
  CTSize sz;
  CTInfo info = lj_ctype_info(cts, id, &sz);
  const CCallInfo *ci = &lj_ir_callinfo[IRCALL_lj_mem_newgco];
  IRRef args[4];
  RegSet drop = RSET_SCRATCH;
  RegSet allow = (RSET_GPR & ~RSET_SCRATCH);
  lj_assertA(sz != CTSIZE_INVALID || (ir->o == IR_CNEW && ir->op2 != REF_NIL),
             "bad CNEW/CNEWI operands");
  as->gcsteps++;
  if (ra_hasreg(ir->r))
    rset_clear(drop, ir->r);  /* Dest reg handled below. */
  ra_evictset(as, drop);
  if (ra_used(ir))
    ra_destreg(as, ir, RID_RET);  /* GCcdata * */

  /* Initialize immutable cdata object. */
  if (ir->o == IR_CNEWI) {
    emit_alopf3_ri(as, 0, sz == 8 ? E2K_STD : E2K_STW, RID_RET,
                   (intptr_t)sizeof(GCcdata),
                   ra_alloc1(as, ir->op2, allow), &as->mcp);
    lj_assertA(sz == 4 || sz == 8, "bad CNEWI size %d", sz);
  } else if (ir->op2 != REF_NIL) { /* Create VLA/VLS/aligned cdata. */
    ci = &lj_ir_callinfo[IRCALL_lj_cdata_newv];
    args[0] = ASMREF_L;     /* lua_State *L */
    args[1] = ir->op1;      /* CTypeID id   */
    args[2] = ir->op2;      /* CTSize sz    */
    args[3] = ASMREF_TMP1;  /* CTSize align */
    asm_gencall(as, ci, args);
    emit_loadi(as, ra_releasetmp(as, ASMREF_TMP1), (int32_t)ctype_align(info));
    return;
  }

  /* Initialize gct and ctypeid. lj_mem_newgco() already sets marked. */
  Reg tmp1 = ra_scratch(as, allow);
  Reg tmp2 = ra_scratch(as, rset_clear(allow, tmp1));
  emit_alopf3_ri(as, 0, E2K_STB, RID_RET, (intptr_t)offsetof(GCcdata, gct),
                 tmp1, 0);
  emit_alopf3_ri(as, 0, E2K_STH, RID_RET, (intptr_t)offsetof(GCcdata, ctypeid),
                 tmp2, &as->mcp);
  emit_alopf1_ii(as, 0, E2K_ADDD, 0, (intptr_t)(~LJ_TCDATA), tmp1, 0);
  emit_alopf1_ii(as, 0, E2K_ADDD, 0, (intptr_t)id, tmp2, &as->mcp);
  args[0] = ASMREF_L;     /* lua_State *L */
  args[1] = ASMREF_TMP1;  /* MSize size   */
  asm_gencall(as, ci, args);
  emit_loadi(as, ra_releasetmp(as, ASMREF_TMP1), (int32_t)(sz+sizeof(GCcdata)));
}
#endif

/* -- Write barriers ------------------------------------------------------ */

static void asm_tbar(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_GPR;
  Reg tab = ra_alloc1(as, ir->op1, allow);
  allow = rset_exclude(allow, tab);
  Reg mark = ra_scratch(as, allow);
  Reg link = ra_scratch(as, rset_exclude(allow, mark));
  Reg tmp = link;
  MCLabel l_end = emit_label(as);
  emit_alopf3_ri(as, 0, E2K_STD, tab, (intptr_t)offsetof(GCtab, gclist),
                 link, &as->mcp);
  emit_alopf3_ri(as, 0, E2K_STB, tab, (intptr_t)offsetof(GCtab, marked),
                 mark, &as->mcp);
  emit_setgl(as, tab, gc.grayagain);
  emit_getgl(as, link, gc.grayagain);
  /* Clear black bit. */
  emit_alopf1_rr(as, 0, E2K_XORD, tmp, mark, mark, &as->mcp);
  Reg pred = ra_pred(as, RSET_PRED);
  emit_ibranch(as, (ptrdiff_t)((void *)l_end - (void *)as->mcp),
               pred, 0, &as->mcp);
  emit_alopf7_ri(as, 0, E2K_CMPEDB, tmp, 0, pred, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_ANDD, mark, LJ_GC_BLACK, tmp, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_LDB, tab, (intptr_t)offsetof(GCtab, marked),
                 mark, &as->mcp);
}

static void asm_obar(ASMState *as, IRIns *ir)
{
  const CCallInfo *ci = &lj_ir_callinfo[IRCALL_lj_gc_barrieruv];
  IRRef args[2];
  MCLabel l_end;
  RegSet allow = RSET_GPR;
  Reg obj = RID_NONE, val = RID_NONE, tmp1 = RID_NONE, tmp2 = RID_NONE;
  Reg pred1 = ra_pred(as, RSET_PRED);
  Reg pred2 = ra_pred(as, rset_exclude(RSET_PRED, pred1));
  Reg ctpr = ra_ctpr(as, RSET_CTPR);
  /* No need for other object barriers (yet). */
  lj_assertA(IR(ir->op1)->o == IR_UREFC, "bad OBAR type");
  ra_evictset(as, RSET_SCRATCH);
  l_end = emit_label(as);
  args[0] = ASMREF_TMP1;  /* global_State *g */
  args[1] = ir->op1;      /* TValue *tv      */
  asm_gencall(as, ci, args);
  emit_loada(as, ra_releasetmp(as, ASMREF_TMP1), J2G(as->J));
  obj = IR(ir->op1)->r;
  val = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, obj));
  tmp1 = ra_scratch(as, rset_clear(allow, obj));
  tmp2 = ra_scratch(as, rset_clear(allow, tmp1));
  emit_ct(as, ctpr, pred1, 0, &as->mcp);
  emit_ct(as, ctpr, pred2, 0, &as->mcp);
  emit_alopf7_ri(as, 0, E2K_CMPESB, tmp1, 0, pred1, 0);
  emit_alopf7_ri(as, 0, E2K_CMPESB, tmp2, 0, pred2, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_ANDS, tmp1, (intptr_t)LJ_GC_BLACK, tmp1, 0);
  emit_alopf1_ri(as, 0, E2K_ANDS, tmp2, (intptr_t)LJ_GC_WHITES, tmp2, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_LDB, obj, (intptr_t)offsetof(GCupval, marked) -
                                      (intptr_t)offsetof(GCupval, tv), tmp1, 0);
  emit_alopf1_ri(as, 0, E2K_LDB, val, (intptr_t)offsetof(GChead, marked),
                 tmp2, 0);
  ptrdiff_t disp = (ptrdiff_t)((void *) l_end - (void *)as->mcp);
  emit_copf2(as, E2K_DISP, ctpr, disp, &as->mcp);
}

/* -- FP/int arithmetic and logic operations ------------------------------ */

static void asm_alopf1(ASMState *as, IRIns *ir, int op)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
  Reg right = RID_NONE;
  if (irref_isk(ir->op2)) {
    emit_alopf1_ri(as, 0, op, left, get_kval(as, ir->op2), dest, &as->mcp);
  } else {
    right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    emit_alopf1_rr(as, 0, op, left, right, dest, &as->mcp);
  }
}

static void asm_arithov(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_GPR;
  lj_assertA(!irt_is64(ir->t), "bad usage");
  Reg dest = ra_dest(as, ir, allow);
  Reg left = ra_alloc1(as, ir->op1, rset_clear(allow, dest));
  Reg right = RID_NONE, tmp1 = RID_NONE, tmp2 = RID_NONE;
  Reg pred = ra_pred(as, RSET_PRED);
  if (irref_isk(ir->op2)) {
    /* (dest < left) == (k >= 0 ? 1 : 0) */
    int k = IR(ir->op2)->i;
    if (ir->o == IR_SUBOV) k = (int)(~(unsigned int)k+1u);
    asm_guard(as, pred, k >= 0 ? 0 : 1);
    emit_alopf7_rr(as, 0, E2K_CMPLSB, dest, left, pred, &as->mcp);
    emit_alopf1_ri(as, 0, E2K_ADDS, left, k, dest, &as->mcp);
  } else {
    /* ((dest^left) & (dest^(~)right)) < 0 */
    right = ra_alloc1(as, ir->op2, rset_clear(allow, left));
    tmp1 = ra_scratch(as, rset_clear(allow, right));
    tmp2 = ra_scratch(as, rset_clear(allow, tmp1));
    asm_guard(as, pred, 0);
    emit_alopf7_ri(as, 0, E2K_CMPLSB, tmp1, 0, pred, &as->mcp);
    emit_alopf1_rr(as, 0, E2K_ANDS, tmp1, tmp2, tmp1, &as->mcp);
    emit_alopf1_rr(as, 0, E2K_XORS, dest, left, tmp1, 0);
    emit_alopf1_rr(as, 0, ir->o == IR_ADDOV ? E2K_XORS : E2K_XORNS,
                   dest, right, tmp2, &as->mcp);
    emit_alopf1_rr(as, 0, ir->o == IR_ADDOV ? E2K_ADDS : E2K_SUBS,
                   left, right, dest, &as->mcp);
  }
}

static void asm_fpmath(ASMState *as, IRIns *ir)
{
  IRFPMathOp fpm = (IRFPMathOp)ir->op2;
  if (fpm == IRFPM_SQRT) {
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg left = ra_alloc1(as, ir->op1, rset_exclude(RSET_GPR, dest));
    emit_alopf11_rr(as, 0, E2K_FSQRTTD, left, dest, dest, &as->mcp);
    emit_alopf12_r(as, 0, E2K_FSQRTID, left, dest, &as->mcp);
  /* floor(0x1), ceil(0x2), trunc(0x3) */
  } else if (fpm <= IRFPM_TRUNC) {
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
    emit_alopf11_ir(as, 0, E2K_FDTOIFD, fpm+1, left, dest, &as->mcp);
  } else {
    asm_callid(as, ir, IRCALL_lj_vm_floor + fpm);
  }
}

static void asm_bnot(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
  emit_alopf1_ri(as, 0, irt_is64(ir->t) ? E2K_XORD : E2K_XORS,
                 left, -1, dest, &as->mcp);
}

static void asm_bswap(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
  Reg smask = ra_scratch(as, rset_exclude(RSET_GPR, left));
  if (irt_is64(ir->t)) {
    emit_alopf21_rrr(as, 0, E2K_PSHUFB, left, left, smask, dest, &as->mcp);
    emit_alopf1_ii(as, 0, E2K_ADDD, 0, 0x1020304050607, smask, &as->mcp);
  } else {
    emit_alopf21_rrr(as, 0, E2K_PSHUFB, left, left, smask, dest, &as->mcp);
    emit_alopf1_ii(as, 0, E2K_ADDD, 0, 0x8080808000010203, smask, 0);
    emit_alopf1_ir(as, 0, E2K_SXT, SXT_WZ, left, left, &as->mcp);
  }
}

static void asm_mul(ASMState *as, IRIns *ir)
{
  if (irt_isnum(ir->t)) {
    asm_alopf1(as, ir, E2K_FMULD);
  } else {
    /* alopf11 for muls/muld */
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg right = RID_NONE, left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
    uint32_t op = irt_is64(ir->t) ? E2K_MULD : E2K_MULS;
    if (irref_isk(ir->op2)) {
      emit_alopf11_ri(as, 0, op, left, get_kval(as, ir->op2), dest, &as->mcp);
    } else {
      right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
      emit_alopf11_rr(as, 0, op, left, right, dest, &as->mcp);
    }
  }
}

static void asm_fpdiv(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
  Reg right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
  emit_alopf11_rr(as, 0, E2K_FDIVD, left, right, dest, &as->mcp);
}

static void asm_neg(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
  if (irt_isnum(ir->t)) {
    emit_alopf1_ri(as, 0, E2K_XORD, left, 0x8000000000000000, dest, &as->mcp);
  } else {
    emit_alopf1_ir(as, 0, irt_is64(ir->t) ? E2K_SUBD : E2K_SUBS,
                   0, left, dest, &as->mcp);
  }
}

static void asm_abs(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);;
  emit_alopf1_ri(as, 0, E2K_ANDD, left, 0x7fffffffffffffff, dest, &as->mcp);
}

static void asm_min_max(ASMState *as, IRIns *ir, int ismax)
{
  if (irt_isnum(ir->t)) {
    asm_alopf1(as, ir, ismax ? E2K_FMAXD : E2K_FMIND);
  } else {
    Reg dest = ra_dest(as, ir, RSET_GPR);
    Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
    Reg right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    // rset can be ignored if register was already allocated
    if (left == right) {
      if (dest != left) emit_movrr(as, 0, dest, left);
    } else {
      Reg pred = ra_pred(as, RSET_PRED);
      emit_mrgc(as, emit_alopf1_rr(as, 1, E2K_MERGES, left, right, dest, 0),
                pred, ismax ? 0 : 1, &as->mcp);
      emit_alopf7_rr(as, 0, E2K_CMPLSB, left, right, pred, &as->mcp);
    }
  }
}

#define asm_min(as, ir)   asm_min_max(as, ir, 0)
#define asm_max(as, ir)   asm_min_max(as, ir, 1)

static void asm_mulov(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
  Reg right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
  Reg tmp = ra_scratch(as, rset_exclude(RSET_GPR, dest));
  Reg pred = ra_pred(as, RSET_PRED);
  asm_guard(as, pred, 1);
  emit_alopf7_rr(as, 0, E2K_CMPEDB, tmp, dest, pred, &as->mcp);
  emit_alopf1_ir(as, 0, E2K_SXT, SXT_WS, dest, tmp, &as->mcp);
  emit_alopf11_rr(as, 0, E2K_SMULX, left, right, dest, &as->mcp);
}

#define asm_addov(as, ir) asm_arithov(as, ir)
#define asm_subov(as, ir) asm_arithov(as, ir)

#define asm_sub(as, ir)   asm_alopf1(as, ir, irt_isnum(ir->t) ? E2K_FSUBD : \
                                             (irt_is64(ir->t) ? E2K_SUBD : E2K_SUBS))
#define asm_add(as, ir)   asm_alopf1(as, ir, irt_isnum(ir->t) ? E2K_FADDD : \
                                             (irt_is64(ir->t) ? E2K_ADDD : E2K_ADDS))
#define asm_bor(as, ir)   asm_alopf1(as, ir, irt_is64(ir->t) ? E2K_ORD : E2K_ORS)
#define asm_bxor(as, ir)  asm_alopf1(as, ir, irt_is64(ir->t) ? E2K_XORD : E2K_XORS)
#define asm_band(as, ir)  asm_alopf1(as, ir, irt_is64(ir->t) ? E2K_ANDD : E2K_ANDS)
#define asm_bshr(as, ir)  asm_alopf1(as, ir, irt_is64(ir->t) ? E2K_SHRD : E2K_SHRS)
#define asm_bshl(as, ir)  asm_alopf1(as, ir, irt_is64(ir->t) ? E2K_SHLD : E2K_SHLS)
#define asm_bsar(as, ir)  asm_alopf1(as, ir, irt_is64(ir->t) ? E2K_SARD : E2K_SARS)
#define asm_bror(as, ir)  asm_alopf1(as, ir, irt_is64(ir->t) ? E2K_SCRD : E2K_SCRS)
#define asm_brol(as, ir)  asm_alopf1(as, ir, irt_is64(ir->t) ? E2K_SCLD : E2K_SCLS)
/* -- Comparisons --------------------------------------------------------- */

static const uint32_t asm_compmap[IR_ABC+1] = {
  /* cmpop  op              invert?  */
  /* LT  */ E2K_CMPLSB,  /* inverted */
  /* GE  */ E2K_CMPLSB,
  /* LE  */ E2K_CMPLESB, /* inverted */
  /* GT  */ E2K_CMPLESB,
  /* ULT */ E2K_CMPBSB,  /* inverted */
  /* UGE */ E2K_CMPBSB,
  /* ULE */ E2K_CMPBESB, /* inverted */
  /* UGT */ E2K_CMPBESB,
  /* EQ  */ E2K_CMPESB,  /* inverted */
  /* NE  */ E2K_CMPESB,
  /* ABC */ E2K_CMPBESB, /* same as UGT */
};

static const uint32_t asm_fpcompmap[IR_ABC+1] = {
  /* cmpop  op                invert?        swap? */
  /* LT  */ E2K_FCMPLTDB,  /* inverted */
  /* GE  */ E2K_FCMPLEDB,  /* inverted */ /* swap  */
  /* LE  */ E2K_FCMPLEDB,  /* inverted */
  /* GT  */ E2K_FCMPLTDB,  /* inverted */ /* swap */
  /* ULT */ E2K_FCMPNLEDB, /* inverted */ /* swap */
  /* UGE */ E2K_FCMPNLTDB, /* inverted */
  /* ULE */ E2K_FCMPNLTDB, /* inverted */ /* swap */
  /* UGT */ E2K_FCMPNLEDB, /* inverted */
  /* EQ  */ E2K_FCMPEQDB,  /* inverted */
  /* NE  */ E2K_FCMPEQDB,
  /* ABC */ E2K_FCMPNLEDB, /* inverted */ /* same as UGT */
};

static void asm_comp(ASMState *as, IRIns *ir)
{
  IROp cmpop = ir->o;
  int inverted = 0, op = 0;
  IRRef lref = ir->op1;
  IRRef rref = ir->op2;
  if (cmpop == IR_ABC) cmpop = IR_UGT;
  if (irt_isnum(ir->t)) {
    inverted = (cmpop == IR_NE) ? 0 : 1;
    op = asm_fpcompmap[cmpop];
    if ((cmpop == IR_GE) || (cmpop == IR_GT) ||
        (cmpop == IR_ULT) || (cmpop == IR_ULE)) {
      IRRef tmp = lref; lref = rref; rref = tmp;
    }
  } else {
    inverted = (cmpop&1) ? 0 : 1;
    /* 5 = E2K_CMPBDB - E2K_CMPBSB */
    op = asm_compmap[cmpop] + (irt_is64(ir->t) ? 5 : 0);
  }
  Reg pred = ra_pred(as, RSET_PRED);
  Reg left = ra_alloc1(as, lref, RSET_GPR);
  asm_guard(as, pred, inverted);

  if (irref_isk(rref)) {
    intptr_t k = get_kval(as, rref);
    emit_alopf7_ri(as, 0, op, left, k, pred, &as->mcp);
  } else {
    Reg right = ra_alloc1(as, rref, rset_exclude(RSET_GPR, left));
    emit_alopf7_rr(as, 0, op, left, right, pred, &as->mcp);
  }
}

#define asm_equal(as, ir) asm_comp(as, ir)

/* -- Split register ops -------------------------------------------------- */

/* Hiword op of a split 32/32 or 64/64 bit op. Previous op is the loword op. */
static void asm_hiop(ASMState *as, IRIns *ir)
{
  /* HIOP is marked as a store because it needs its own DCE logic. */
  int uselo = ra_used(ir-1), usehi = ra_used(ir);  /* Loword/hiword used? */
  if (LJ_UNLIKELY(!(as->flags & JIT_F_OPT_DCE))) uselo = usehi = 1;
  if (!usehi) return;  /* Skip unused hiword op for all remaining ops. */
  switch ((ir-1)->o) {
  case IR_CALLN: case IR_CALLL: case IR_CALLS: case IR_CALLXS:
    if (!uselo)
      ra_allocref(as, ir->op1, RID2RSET(RID_RETLO));  /* Mark lo op as used. */
    break;
  default: lj_assertA(0, "bad HIOP for op %d", (ir-1)->o); break;
  }
}

/* -- Profiling ----------------------------------------------------------- */

static void asm_prof(ASMState *as, IRIns *ir)
{
  UNUSED(ir);
  Reg tmp = ra_scratch(as, RSET_GPR);
  Reg pred = ra_pred(as, RSET_PRED);
  asm_guard(as, pred, 1);
  emit_alopf7_ri(as, 0, E2K_CMPANDESB, tmp, HOOK_PROFILE, pred, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_LDB, RID_DISPATCH,
                 (int32_t)dispofs(as, &J2G(as->J)->hookmask), tmp, &as->mcp);
}

/* -- Stack handling ------------------------------------------------------ */

/* Check Lua stack size for overflow. Use exit handler as fallback. */
static void asm_stack_check(ASMState *as, BCReg topslot,
                            IRIns *irp, RegSet allow, ExitNo exitno)
{
  /* Try to get an unused temp register, otherwise use RID_TMP*. */
  Reg pbase = irp ? (ra_hasreg(irp->r) ? irp->r : RID_TMP2) : RID_BASE;
  ExitNo oldsnap = as->snapno;
  allow = rset_exclude(allow, pbase);
  Reg tmp = allow ? rset_pickbot(allow) : RID_TMP3;
  Reg pred = ra_pred(as, RSET_PRED);
  as->snapno = exitno;
  asm_guard(as, pred, 0);
  as->snapno = oldsnap;
  emit_alopf7_ri(as, 0, E2K_CMPBDB, tmp, (intptr_t)(8*topslot),
                 pred, &as->mcp);
  if (allow != RSET_EMPTY) ra_modified(as, tmp);
  emit_alopf1_rr(as, 0, E2K_SUBD, tmp, pbase, tmp, &as->mcp);
  emit_alopf1_ri(as, 0, E2K_LDD, tmp, (intptr_t)offsetof(lua_State, maxstack),
                 tmp, &as->mcp);
  if (pbase == RID_TMP2)
    emit_getgl(as, RID_TMP2, jit_base);
  emit_getgl(as, tmp, cur_L);
}

/* Restore Lua stack from on-trace state. */
static void asm_stack_restore(ASMState *as, SnapShot *snap)
{
  RegSet allow = rset_exclude(RSET_GPR, RID_BASE);
  SnapEntry *map = &as->T->snapmap[snap->mapofs];
  MSize n, nent = snap->nent;
  /* Store the value of all modified slots to the Lua stack. */
  for (n = 0; n < nent; n++) {
    SnapEntry sn = map[n];
    BCReg s = snap_slot(sn);
    int32_t ofs = 8*((int32_t)s-1-LJ_FR2);
    IRRef ref = snap_ref(sn);
    IRIns *ir = IR(ref);
    if ((sn & SNAP_NORESTORE))
      continue;
    if ((sn & SNAP_KEYINDEX)) {
      int64_t kki = (int64_t)LJ_KEYINDEX << 32;
      if (irref_isk(ref)) {
        kki = kki | (int64_t)(uint32_t)ir->i;
        Reg rki = ra_allock(as, kki, allow);
        emit_alopf3_ri(as, 0, E2K_STD, RID_BASE, ofs, rki, &as->mcp);
      } else {
        Reg src = ra_alloc1(as, ref, allow);
        allow = rset_exclude(allow, src);
        Reg tmp = ra_scratch(as, allow);
        emit_alopf3_ri(as, 0, E2K_STD, RID_BASE, ofs, tmp, &as->mcp);
        emit_alopf1_ri(as, 0, E2K_ADDD, src, kki, tmp, &as->mcp);
      }
    } else if (irt_isnum(ir->t)) {
      Reg src = ra_alloc1(as, ref, allow);
      emit_alopf3_ri(as, 0, E2K_STD, RID_BASE, ofs, src, &as->mcp);
    } else {
      lj_assertA(irt_ispri(ir->t) || irt_isaddr(ir->t) || irt_isinteger(ir->t),
                 "store of IR type %d", irt_type(ir->t));
      if (irref_isk(ref)) {
        TValue k;
        lj_ir_kvalue(as->J->L, &k, ir);
        Reg rki = ra_allock(as, (int64_t)k.u64, allow);
        emit_alopf3_ri(as, 0, E2K_STD, RID_BASE, ofs, rki, &as->mcp);
      } else {
        Reg src = ra_alloc1(as, ref, allow);
        allow = rset_exclude(allow, src);
        int64_t type = (int64_t)irt_toitype(ir->t) << 47;
        Reg tmp = ra_scratch(as, allow);
        emit_alopf3_ri(as, 0, E2K_STD, RID_BASE, ofs, tmp, &as->mcp);
        if (irt_isinteger(ir->t)) {
          emit_alopf1_ri(as, 0, E2K_ADDD, tmp, type, tmp, &as->mcp);
          emit_alopf1_ir(as, 0, E2K_SXT, SXT_WZ, src, tmp, &as->mcp);
        } else {
          emit_alopf1_ri(as, 0, E2K_ADDD, src, type, tmp, &as->mcp);
        }
      }
    }
    checkmclim(as);
  }
}

/* -- GC handling --------------------------------------------------------- */

/* Marker to prevent patching the GC check exit. */
/* ord 0x0, 0x0, empty.hi */
#define E2K_NOPATCH_GC_CHECK_HS 0x4000001
#define E2K_NOPATCH_GC_CHECK    0x5c0c0df

/* Check GC threshold and do one or more GC steps. */
static void asm_gc_check(ASMState *as)
{
  const CCallInfo *ci = &lj_ir_callinfo[IRCALL_lj_gc_step_jit];
  IRRef args[2];
  MCLabel l_end;
  Reg tmp1, tmp2;
  ra_evictset(as, RSET_SCRATCH);
  l_end = emit_label(as);
  /* Exit trace if in GCSatomic or GCSfinalize. Avoids syncing GC objects. */
  /* Assumes asm_snap_prep() already done. */
  Reg pred = ra_pred(as, RSET_PRED);
  asm_guard(as, pred, 1);
  *--as->mcp = E2K_NOPATCH_GC_CHECK;
  *--as->mcp = E2K_NOPATCH_GC_CHECK_HS;
  emit_alopf7_ri(as, 0, E2K_CMPEDB, RID_RET, 0, pred, &as->mcp);
  args[0] = ASMREF_TMP1;  /* global_State *g */
  args[1] = ASMREF_TMP2;  /* MSize steps     */
  asm_gencall(as, ci, args);
  tmp1 = ra_releasetmp(as, ASMREF_TMP1);
  emit_alopf1_ri(as, 0, E2K_ADDD, RID_DISPATCH, GG_DISP2G, tmp1, &as->mcp);
  tmp2 = ra_releasetmp(as, ASMREF_TMP2);
  emit_loadi(as, tmp2, as->gcsteps);
  /* Jump around GC step if GC total < GC threshold. */
  emit_ibranch(as, (ptrdiff_t)((void *)l_end - (void *)as->mcp),
               pred, 0, &as->mcp);
  emit_alopf7_rr(as, 0, E2K_CMPBDB, tmp1, tmp2, pred, &as->mcp);
  emit_getgl(as, tmp1, gc.total);
  emit_getgl(as, tmp2, gc.threshold);
  as->gcsteps = 0;
  checkmclim(as);
}

/* -- Loop handling ------------------------------------------------------- */

static void asm_loop_fixup(ASMState *as)
{
  MCode *p = as->mctop;
  MCode *target = as->mcp;
  p[-1] = E2K_NOP; p[-2] = E2K_NOP; p[-3] = E2K_NOP; p[-4] = E2K_NOP;
  p = p - 4; /* skip nops */
  /* p[-4] - HS; p[-3] - SS; p[-2] - CS0; p[-1] - Align */
  if (as->loopinv) { /* Inverted loop branch? */
    /* asm_guard already inverted the cond branch. Only patch the target. */
    uint32_t tmp = p[-2] & 0xf0000000;
    uint32_t disp = (ptrdiff_t)((void *)target - (void *)p + 4*4) >> 3;
    p[-2] = tmp | (disp & 0xfffffff);
  } else { /* 4(HS+SS+CS0+Align) */
    emit_ibranch(as, (ptrdiff_t)((void *)target - (void *)p), 0, 0, &p);
  }
}

static void asm_loop_tail_fixup(ASMState *as)
{
  if (as->loopinv) as->mctop -= 4;
}

/* -- Head of trace ------------------------------------------------------- */

/* Coalesce BASE register for a root trace. */
static void asm_head_root_base(ASMState *as)
{
  IRIns *ir = IR(REF_BASE);
  Reg r = ir->r;
  if (ra_hasreg(r)) {
    ra_free(as, r);
    if (rset_test(as->modset, r) || irt_ismarked(ir->t))
      ir->r = RID_INIT; /* No inheritance for modified BASE register. */
    if (r != RID_BASE)
      emit_movrr(as, 0, r, RID_BASE);
  }
}

/* Coalesce BASE register for a side trace. */
static Reg asm_head_side_base(ASMState *as, IRIns *irp)
{
  IRIns *ir = IR(REF_BASE);
  Reg r = ir->r;
  if (ra_hasreg(r)) {
    ra_free(as, r);
    if (rset_test(as->modset, r) || irt_ismarked(ir->t))
      ir->r = RID_INIT; /* No inheritance for modified BASE register. */
    if (irp->r == r) {
      return r;  /* Same BASE register already coalesced. */
    } else if (ra_hasreg(irp->r) && rset_test(as->freeset, irp->r)) {
      emit_movrr(as, 0, r, irp->r); /* Move from coalesced parent reg. */
      return irp->r;
    } else {
      emit_getgl(as, r, jit_base);  /* Otherwise reload BASE. */
    }
  }
  return RID_NONE;
}


/* -- Tail of trace ------------------------------------------------------- */

/* Fixup the tail code. */
static void asm_tail_fixup(ASMState *as, TraceNo lnk)
{
  MCode *target = lnk ? traceref(as->J, lnk)->mcode : (MCode *)lj_vm_exit_interp;
  MCode *p = as->mctop;
  int32_t spadj = as->T->spadjust;
  emit_ibranch(as, (ptrdiff_t)((void *)target - (void *)p), 0, 0, &p);
  /* 4(HS+SS+CS0+Align) */
  if (spadj) {
    emit_alopf12_i(as, 0, E2K_GETSP, spadj, RID_SP, &p);
    /* 4(HS+ALS+ALES+LTS) */
  } else {
    p[-1] = E2K_NOP; p[-2] = E2K_NOP; p[-3] = E2K_NOP; p[-4] = E2K_NOP;
  }
}

/* Prepare tail of code. */
static void asm_tail_prep(ASMState *as)
{
  /* initialized by zero, it counts as nop */
  as->mcp = as->mctop - 8;
  as->invmcp = as->loopref ? as->mcp : NULL;
}

/* -- Trace setup --------------------------------------------------------- */

/* Ensure there are enough stack slots for call arguments. */
static Reg asm_setup_call_slots(ASMState *as, IRIns *ir, const CCallInfo *ci)
{
  IRRef args[CCI_NARGS_MAX*2];
  uint32_t nargs = CCI_XNARGS(ci);
  int nslots = 0, ngpr = REGARG_NUMGPR;
  int is_vararg = ci->flags & CCI_VARARG;
  asm_collectargs(as, ir, ci, args);
  /* empty slots for first 8 args or slots if vararg */
  if ((nargs > ngpr) || is_vararg)
    nslots = nargs * 2;
  if (nslots > as->evenspill) /* Leave room for args in stack slots. */
    as->evenspill = nslots;
  return REGSP_HINT(RID_RET);
}

/* Target-specific setup. */
static void asm_setup_target(ASMState *as)
{
  emit_bundle_setup(as);
  asm_exitstub_setup(as);
}

/* -- Trace patching ------------------------------------------------------ */

/* Patch exit jumps of existing machine code to a new target. */
void lj_asm_patchexit(jit_State *J, GCtrace *T, ExitNo exitno, MCode *target)
{
  MCode *p = T->mcode;
  MCode *pe = (MCode *)((char *)p + T->szmcode);
  MCode *px = exitstub_trace_addr(T, exitno);
  MCode *cstart = NULL, *cstop = NULL;
  MCode *mcarea = lj_mcode_patch(J, p, 0);
  /* Look for addd  0, exitno(lts32), TMP0, (predN) */
  MCode exitload = 0x11c0d8f0;
  for (p++; p < pe; p++) {
    if (*p == exitload) { /* Look for load of exit number. */
      if (p[2] != exitno) continue;
      /* p[-3] - E2K_NOPATCH_GC_CHECK_HS; p[-2] - E2K_NOPATCH_GC_CHECK. */
      /* p[-1] - HS; p[0] - ALS; p[1] - hole; p[2] - LTS. */
      /* p[3] - HS; p[4] - SS; p[5] - CS0; p[6] - Align. */
      /* Look for exitstub branch. */
      uint32_t disp = (ptrdiff_t)((void *)px - (void *)p - 3*4) >> 3;
      if ((p[5] ^ (disp & 0xfffffff)) == 0 && p[-2] != E2K_NOPATCH_GC_CHECK) {
        disp = (ptrdiff_t)((void *)target - (void *)p - 3*4) >> 3;
        p[5] = disp & 0xfffffff;
        /* Replace the load of the exit number with nops. */
        p[-1] = E2K_NOP; p[0] = E2K_NOP; p[1] = E2K_NOP; p[2] = E2K_NOP;
        cstop = p + 7;
        if (!cstart) cstart = p - 1;
      } else if (p+7 == pe) {
        /* Patch NOP after code for inverted loop branch. Use of J is ok. */
        lj_assertJ(p[7] == E2K_NOP, "expected NOP");
        /* Replace the load of the exit number with nops. */
        p[-1] = E2K_NOP; p[0] = E2K_NOP; p[1] = E2K_NOP; p[2] = E2K_NOP;
        disp = (ptrdiff_t)((void *)target - (void *)p - 7*4) >> 3;
        /* ibranch target */
        p[7] = 0x5012; /* HS */
        p[8] = 0xc0000020; /* SS */
        p[9] = disp & 0xfffffff; /* CS0 */
        p[10] = 0; /* Align */
        cstop = p + 11;
        if (!cstart) cstart = p - 1;
      }
    }
  }
  if (cstart) lj_mcode_sync(cstart, cstop);
  lj_mcode_patch(J, mcarea, 1);
}

