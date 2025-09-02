/*
** E2K IR assembler (SSA IR -> machine code).
** Copyright (C) 2005-2025 Mike Pall. See Copyright Notice in luajit.h
*/

#define NIY __builtin_trap();

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
  /*
    stw STACK, STACK_TMP, TMP0
    addd  0, as->T->traceno, TMP0
    ibranch ->lj_vm_exit_handler
  */

  /* Register allocation is not started yet */
  MCode *mxp = as->mctop;
  /* Should be in separate bundle for patchexit */
  emit_ibranch(as, (ptrdiff_t)((void *)lj_vm_exit_handler - (void *)mxp), 0, 0);
  mxp = emit_bundle_finalize(as, mxp);
  emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                emit_src1(as, E2K_CONST, 0),
                emit_lts(as, E2K_CONST32, as->T->traceno) | 0xd8,
                emit_dst(as, E2K_REG, RID_TMP));
  mxp = emit_bundle_finalize(as, mxp);
  emit_alopf3(as, 0, OPC_STW, RES_ALS_25,
                emit_src1(as, E2K_REG, RID_SP),
                emit_src2(as, E2K_CONST, SPOFS_TMP),
                emit_src3(as, E2K_REG, RID_TMP));
  mxp = emit_bundle_finalize(as, mxp);

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
  /*
    addd snapno(32), TMP0, pred
    ibranch target, pred
  */
  emit_ibranch(as, (ptrdiff_t)((void *)target - (void *)p), pred, inverted);
  as->mcp = emit_bundle_finalize(as, as->mcp);
  int als = emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                        emit_src1(as, E2K_CONST, 0),
                        emit_lts(as, E2K_CONST32, as->snapno) | 0xd8,
                        emit_dst(as, E2K_REG, RID_TMP));
  emit_alu_cond(as, als, pred, inverted);
  as->mcp = emit_bundle_finalize(as, as->mcp);
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

/* -- Calls --------------------------------------------------------------- */

/* Generate a call to a C function. */
static void asm_gencall(ASMState *as, const CCallInfo *ci, IRRef *args)
{
  uint32_t n, nargs = CCI_XNARGS(ci);
  int32_t ofs = ci->flags & CCI_VARARG ? 0 : STACKARG_OFS;
  Reg gpr = RID_NONE;
  Reg ctpr = ra_ctpr(as, RSET_CTPR);
  if (ci->func) {
    emit_call(as, ctpr, 0, 0, PIPE_WBS);
    as->mcp = emit_bundle_finalize(as, as->mcp);
  }
  for (gpr = REGARG_FIRSTGPR; gpr <= REGARG_LASTGPR; gpr++)
    as->cost[gpr] = REGCOST(~0u, ASMREF_L);
  gpr = REGARG_FIRSTGPR;
  for (n = 0; n < nargs; n++) { /* Setup args. */
    IRRef ref = args[n];
    if (ref) {
      //IRIns *ir = IR(ref);
      if (gpr <= REGARG_LASTGPR) {
        lj_assertA(rset_test(as->freeset, gpr),
                   "arg%d not free", gpr-REGARG_FIRSTGPR); /*  Already evicted. */
        ra_leftov(as, gpr, ref);
        if (ci->flags & CCI_VARARG) {
          NIY
        }
        gpr++;
      } else {
        NIY
        /* Reg r = ra_alloc1(as, ref, RSET_GPR);
        emit_spstore(as, ir, r, ofs);
        ofs += 8; */
      }
    } else {
      NIY
      if (gpr <= REGARG_LASTGPR) {
        gpr++;
      } else {
        ofs += 8;
      }
    }
    checkmclim(as);
  }
  if (ci->func) {
    emit_prepcall(as, ctpr, ci->func);
    as->mcp = emit_bundle_finalize(as, as->mcp);
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
    if (irt_isfp(ir->t) && (ci->flags & CCI_CASTU64)) {
      NIY
    } else if (hiop) {
      ra_destpair(as, ir);
    } else {
      ra_destreg(as, ir, RID_RET);
    }
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
  emit_alopf7(as, 0, OPC_CMPDB, CMPI_EQ, RES_ALS_0134,
              emit_src1(as, E2K_REG, tmp),
              emit_src2(as, E2K_CONST, (intptr_t)pc),
              emit_pdst(as, E2K_REG_PRED, pred));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  emit_alopf1(as, 0, OPC_LDD, RES_ALS_0235,
              emit_src1(as, E2K_REG, base),
              emit_src2(as, E2K_CONST, LJ_FR2 ? -8 : -4),
              emit_dst(as, E2K_REG, tmp));
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

/* -- Type conversions ---------------------------------------------------- */

static void asm_tointg(ASMState *as, IRIns *ir, Reg left)
{
  Reg pred = ra_pred(as, RSET_PRED);
  Reg tmp = ra_scratch(as, rset_exclude(RSET_GPR, left));
  Reg dest = ra_dest(as, ir, RSET_GPR);
  asm_guard(as, pred, 1);
  /*
    fdtoistr left, dest
    istofd dest, tmp
    fcmpeqdb left, tmp, predN
    asm_guard(inverted)
  */
  emit_alopf7(as, 0, OPC_FCMPDB, CMPF_EQ, RES_ALS_0134,
              emit_src1(as, E2K_REG, left),
              emit_src2(as, E2K_REG, tmp),
              emit_pdst(as, E2K_REG_PRED, pred));
  as->mcp = emit_bundle_finalize(as, as->mcp);

  emit_alopf2(as, 0, OPC_FSTOD, CO_ISTOFD, RES_ALS_0134,
              emit_src2(as, E2K_REG, dest),
              emit_dst(as, E2K_REG, tmp));
  as->mcp = emit_bundle_finalize(as, as->mcp);

  emit_alopf2(as, 0, OPC_FDTOS, CO_FDTOISTR, RES_ALS_0134,
              emit_src2(as, E2K_REG, left),
              emit_dst(as, E2K_REG, dest));
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

// TODO refactor after full implementation
static void asm_conv(ASMState *as, IRIns *ir)
{
  IRType st = (IRType)(ir->op2 & IRCONV_SRCMASK);
  int stfp = (st == IRT_NUM || st == IRT_FLOAT);
  int st64 = (st == IRT_I64 || st == IRT_U64 || st == IRT_P64);
  int cop = 0, opce = 0;
  RegSet allow = RSET_GPR;
  lj_assertA(irt_type(ir->t) != st, "inconsistent types for CONV");
  Reg left = ra_alloc1(as, ir->op1, allow);
  if (irt_isfp(ir->t)) {
    Reg dest = ra_dest(as, ir, allow);
    if (stfp) { /* FP to FP conversion */
      cop = (st == IRT_NUM ? OPC_FDTOS : OPC_FSTOD);
      opce = CO_FSTOFD; /* smae for both cop */
    } else { /* INT to FP conversion */
      cop = (st == IRT_U32 || st == IRT_INT) ?
        (irt_isnum(ir->t) ? OPC_FSTOD : OPC_FSTOS) :
        (irt_isnum(ir->t) ? OPC_FDTOD : OPC_FDTOS);
      opce = CO_ISTOFS; /* smae for all cop */
    }
    emit_alopf2(as, 0, cop, opce, RES_ALS_0134,
                emit_src2(as, E2K_REG, left),
                emit_dst(as, E2K_REG, dest));
    as->mcp = emit_bundle_finalize(as, as->mcp);
  } else if (stfp) { /* FP to INT conversion */
    if (irt_isguard(ir->t)) {
      /* Checked conversions are only supported from NUM to INT */
      lj_assertA(irt_isint(ir->t) && st == IRT_NUM,
                 "bad type for checked CONV");
      asm_tointg(as, ir, left);
    } else {
      Reg dest = ra_dest(as, ir, allow);
      if (irt_isu64(ir->t)) { /* FP to U64 */
        /* for inputs >= 2^63 add -2^64, convert again. */
        NIY
      } else if (irt_isu32(ir->t)) { /* FP to U32 */
        NIY
      } else {
        cop = irt_is64(ir->t) ?
          (st == IRT_NUM ? OPC_FDTOD : OPC_FSTOD) :
          (st == IRT_NUM ? OPC_FDTOS : OPC_FSTOS);
        opce = CO_FSTOISTR; /* same for all cop */
        emit_alopf2(as, 0, cop, opce, RES_ALS_0134,
                    emit_src2(as, E2K_REG, left),
                    emit_dst(as, E2K_REG, dest));
        as->mcp = emit_bundle_finalize(as, as->mcp);
      }
    }
  } else { /* INT to INT conversion */
    NIY
  }
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
    emit_alopf3(as, 0, OPC_STD, RES_ALS_25,
                emit_src1(as, E2K_REG, base),
                emit_src2(as, E2K_CONST, ofs),
                emit_src3(as, E2K_REG, tmp));
    as->mcp = emit_bundle_finalize(as, as->mcp);
  } else {
    Reg src = ra_alloc1(as, ref, allow);
    allow = rset_exclude(allow, src);
    Reg type = ra_allock(as, (int64_t)irt_toitype(ir->t) << 47, allow);
    Reg tmp = ra_scratch(as, allow);
    emit_alopf3(as, 0, OPC_STD, RES_ALS_25,
                emit_src1(as, E2K_REG, base),
                emit_src2(as, E2K_CONST, ofs),
                emit_src3(as, E2K_REG, tmp));
    as->mcp = emit_bundle_finalize(as, as->mcp);
    if (irt_isinteger(ir->t)) {
      emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                  emit_src1(as, E2K_REG, tmp),
                  emit_src2(as, E2K_REG, type),
                  emit_dst(as, E2K_REG, tmp));
      as->mcp = emit_bundle_finalize(as, as->mcp);
      emit_alopf1(as, 0, OPC_SXT, RES_ALS_012345,
                  emit_src1(as, E2K_CONST, SXT_WZ),
                  emit_src2(as, E2K_REG, src),
                  emit_dst(as, E2K_REG, tmp));
      as->mcp = emit_bundle_finalize(as, as->mcp);
    } else {
       emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                  emit_src1(as, E2K_REG, src),
                  emit_src2(as, E2K_REG, type),
                  emit_dst(as, E2K_REG, tmp));
      as->mcp = emit_bundle_finalize(as, as->mcp);
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
        ra_allockreg(as, igcptr(ir_knum(ir)), dest);
      } else {
        emit_movrr(as, ir, dest, ra_alloc1(as, ref, RSET_GPR));
      }
    } else {
      /* Otherwise use g->tmptv to hold the TValue. */
      asm_tvstore64(as, dest, 0, ref);
      emit_loada(as, dest, &J2G(as->J)->tmptv);
    }
  } else {
    emit_loada(as, dest, &J2G(as->J)->tmptv);
  }
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
    emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                emit_src1(as, E2K_REG, base),
                emit_src2(as, E2K_CONST, ofs),
                emit_dst(as, E2K_REG, dest));
    as->mcp = emit_bundle_finalize(as, as->mcp);
  } else {
    base = ra_alloc1(as, ir->op1, allow);
    allow = rset_exclude(allow, base);
    idx = ra_alloc1(as, ir->op2, allow);
    allow = rset_exclude(allow, idx);
    tmp = ra_scratch(as, allow);
    emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                emit_src1(as, E2K_REG, base),
                emit_src2(as, E2K_REG, tmp),
                emit_dst(as, E2K_REG, dest));
    as->mcp = emit_bundle_finalize(as, as->mcp);
    emit_alopf1(as, 0, OPC_SHLD, RES_ALS_012345,
                emit_src1(as, E2K_REG, idx),
                emit_src2(as, E2K_CONST, 3),
                emit_dst(as, E2K_REG, tmp));
    as->mcp = emit_bundle_finalize(as, as->mcp);
    /* if its integer extend first */
    if (irt_isinteger(IR(ir->op2)->t)) {
      emit_alopf1(as, 0, OPC_SXT, RES_ALS_012345,
                  emit_src1(as, E2K_CONST, SXT_WS),
                  emit_src2(as, E2K_REG, idx),
                  emit_dst(as, E2K_REG, idx));
      as->mcp = emit_bundle_finalize(as, as->mcp);
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
  /*
    ldd node, kofs, key
    cmpedb key, k, predN
    asm_guard(inverted)
    addd node, ofs, dest (if needed)
  */
  Reg pred = ra_pred(as, RSET_PRED);
  if (ra_hasreg(dest)) {
    emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                emit_src1(as, E2K_REG, node),
                emit_src2(as, E2K_CONST, ofs),
                emit_dst(as, E2K_REG, dest));
    as->mcp = emit_bundle_finalize(as, as->mcp);
  }
  asm_guard(as, pred, 1);
  emit_alopf7(as, 0, OPC_CMPDB, CMPI_EQ, RES_ALS_0134,
              emit_src1(as, E2K_REG, key),
              emit_src2(as, E2K_CONST, k),
              emit_pdst(as, E2K_REG_PRED, pred));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  emit_alopf1(as, 0, OPC_LDD, RES_ALS_0235,
              emit_src1(as, E2K_REG, node),
              emit_src2(as, E2K_CONST, kofs),
              emit_dst(as, E2K_REG, key));
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

/* -- Loads and stores ---------------------------------------------------- */

static uint32_t asm_loadins(ASMState *as, IRIns *ir, Reg dest)
{
  UNUSED(as);
  uint32_t sxt_cop = 0, need_sxt = 0, cop = 0;
  switch (irt_type(ir->t)) {
  case IRT_I8:
    need_sxt = 1;
    sxt_cop = SXT_BS;
  case IRT_U8:
    cop = OPC_LDB;
    break;
  case IRT_I16:
    need_sxt = 1;
    sxt_cop = SXT_HS;
  case IRT_U16:
    cop = OPC_LDH;
    break;
  default:
    cop = irt_is64(ir->t) ? OPC_LDD : OPC_LDW;
    break;
  }
  /* ldb and ldh unsigned, need sign extension */
  if (need_sxt) {
    emit_alopf1(as, 0, OPC_SXT, RES_ALS_012345,
                emit_src1(as, E2K_CONST, sxt_cop),
                emit_src2(as, E2K_REG, dest),
                emit_dst(as, E2K_REG, dest));
    as->mcp = emit_bundle_finalize(as, as->mcp);
  }
  return cop;
}

static void asm_fload(ASMState *as, IRIns *ir)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg base = RID_NONE;
  int32_t ofs = 0;
  if (ir->op1 == REF_NIL) { /* FLOAD from GG_State with offset. */
    ofs = (int32_t)(ir->op2 << 2) - GG_OFS(dispatch);
    base = RID_DISPATCH;
  } else {
    ofs = field_ofs[ir->op2];
    base = ra_alloc1(as, ir->op1, RSET_GPR);
  }
  uint32_t cop = asm_loadins(as, ir, dest);
  emit_alopf1(as, 0, cop, RES_ALS_0235,
              emit_src1(as, E2K_REG, base),
              emit_src2(as, E2K_CONST, ofs),
              emit_dst(as, E2K_REG, dest));
  as->mcp = emit_bundle_finalize(as, as->mcp);
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
      emit_alopf1(as, 0, OPC_GETFD, RES_ALS_012345,
                  emit_src1(as, E2K_REG, dest),
                  emit_src2(as, E2K_CONST, 0xbc0),
                  emit_dst(as, E2K_REG, dest));
      as->mcp = emit_bundle_finalize(as, as->mcp);
    } else if (irt_isint(t)) {
      emit_alopf1(as, 0, OPC_SXT, RES_ALS_012345,
                  emit_src1(as, E2K_CONST, SXT_WZ),
                  emit_src2(as, E2K_REG, dest),
                  emit_dst(as, E2K_REG, dest));
      as->mcp = emit_bundle_finalize(as, as->mcp);
    }
  }
  base = asm_fuseahuref(as, ir->op1, &ofs, allow);
  allow = rset_exclude(allow, base);
  if (ir->o == IR_VLOAD) ofs += 8 * ir->op2;
  /*
    ldd base, ofs, dest
    sard   dest, 47, type
    cmpesb type, LJ_TYPE, predN
    asm_guard(inverted)
    sxt/getfd dest
  */
  type = ra_scratch(as, allow);
  intptr_t k = irt_isnum(t) ? (int32_t)LJ_TISNUM :
               (int32_t)irt_toitype(t);
  int opce = irt_isnum(t) ? CMPI_B : CMPI_EQ;
  asm_guard(as, pred, 1);
  emit_alopf7(as, 0, OPC_CMPSB, opce, RES_ALS_0134,
              emit_src1(as, E2K_REG, type),
              emit_src2(as, E2K_CONST, k),
              emit_pdst(as, E2K_REG_PRED, pred));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  if (!ra_hasreg(dest)) dest = type;
  emit_alopf1(as, 0, OPC_SARD, RES_ALS_012345,
              emit_src1(as, E2K_REG, dest),
              emit_src2(as, E2K_CONST, 47),
              emit_dst(as, E2K_REG, type));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  emit_alopf1(as, 0, OPC_LDD, RES_ALS_0235,
              emit_src1(as, E2K_REG, base),
              emit_src2(as, E2K_CONST, ofs),
              emit_dst(as, E2K_REG, dest));
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

static void asm_ahustore(ASMState *as, IRIns *ir)
{
  RegSet allow = RSET_GPR;
  Reg base, src = RID_NONE, type = RID_NONE;
  int32_t ofs = 0;
  if (ir->r == RID_SINK)
    return;
  if (irt_isnum(ir->t)) {
    src = ra_alloc1(as, ir->op2, allow);
    allow = rset_exclude(allow, src);
    base = asm_fuseahuref(as, ir->op1, &ofs, allow);
    emit_alopf3(as, 0, OPC_STD, RES_ALS_25,
                emit_src1(as, E2K_REG, base),
                emit_src2(as, E2K_CONST, ofs),
                emit_src3(as, E2K_REG, src));
    as->mcp = emit_bundle_finalize(as, as->mcp);
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
      type = ra_allock(as, (int64_t)irt_toitype(ir->t) << 47, allow);
      allow = rset_exclude(allow, type);
    }
    base = asm_fuseahuref(as, ir->op1, &ofs, allow);
    emit_alopf3(as, 0, OPC_STD, RES_ALS_25,
                emit_src1(as, E2K_REG, base),
                emit_src2(as, E2K_CONST, ofs),
                emit_src3(as, E2K_REG, tmp));
    as->mcp = emit_bundle_finalize(as, as->mcp);
    if (ra_hasreg(src)) {
      if (irt_isinteger(ir->t)) {
        emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                    emit_src1(as, E2K_REG, tmp),
                    emit_src2(as, E2K_REG, type),
                    emit_dst(as, E2K_REG, tmp));
        as->mcp = emit_bundle_finalize(as, as->mcp);
        emit_alopf1(as, 0, OPC_SXT, RES_ALS_012345,
                    emit_src1(as, E2K_CONST, SXT_WZ),
                    emit_src2(as, E2K_REG, src),
                    emit_dst(as, E2K_REG, tmp));
        as->mcp = emit_bundle_finalize(as, as->mcp);
      } else {
        emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                    emit_src1(as, E2K_REG, src),
                    emit_src2(as, E2K_REG, type),
                    emit_dst(as, E2K_REG, tmp));
        as->mcp = emit_bundle_finalize(as, as->mcp);
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
  int cop = 0, opce = 0;
  lj_assertA(!(ir->op2 & IRSLOAD_PARENT),
             "bad parent SLOAD");  /* Handled by asm_head_side(). */
  lj_assertA(irt_isguard(ir->t) || !(ir->op2 & IRSLOAD_TYPECHECK),
             "inconsistent SLOAD variant");
  if ((ir->op2 & IRSLOAD_CONVERT) && irt_isguard(t) && irt_isint(t)) {
    dest = ra_scratch(as, allow);
    allow = rset_exclude(allow, dest);
    asm_tointg(as, ir, dest);
    t.irt = IRT_NUM; /* Continue with a regular number type check. */
  } else if (ra_used(ir)) {
    lj_assertA(irt_isnum(ir->t) || irt_isint(ir->t) || irt_isaddr(ir->t),
               "bad SLOAD type %d", irt_type(t));
    dest = ra_dest(as, ir, allow);
    allow = rset_exclude(allow, dest);
    if (ir->op2 & IRSLOAD_CONVERT) {
      cop = irt_isint(t) ? OPC_FDTOS : OPC_FSTOD;
      opce = irt_isint(t) ? CO_FDTOISTR : CO_ISTOFD;
      t.irt = irt_isint(t) ? IRT_NUM : IRT_INT;
      emit_alopf2(as, 0, cop, opce, RES_ALS_0134,
                  emit_src2(as, E2K_REG, dest),
                  emit_dst(as, E2K_REG, dest));
      as->mcp = emit_bundle_finalize(as, as->mcp);
    } else if (irt_isaddr(t)) {
      /* Clear type from pointers. */
      emit_alopf1(as, 0, OPC_GETFD, RES_ALS_012345,
                  emit_src1(as, E2K_REG, dest),
                  emit_src2(as, E2K_CONST, 0xbc0),
                  emit_dst(as, E2K_REG, dest));
      as->mcp = emit_bundle_finalize(as, as->mcp);
    } else if (irt_isint(t) && (ir->op2 & IRSLOAD_TYPECHECK)) {
      /* Sign-extend integers. */
      // TODO SIGN EXTEND ??
      NIY
    }
  }
  base = ra_alloc1(as, REF_BASE, allow);
  allow = rset_exclude(allow, base);
  if (ir->op2 & IRSLOAD_TYPECHECK) {
    Reg pred = ra_pred(as, RSET_PRED);
    Reg type = ra_scratch(as, allow);
    if (!ra_hasreg(dest))
      dest = type;
    if (irt_ispri(t)) {
      asm_guard(as, pred, 1);
      intptr_t k = ~((int64_t)~irt_toitype(t) << 47);
      emit_alopf7(as, 0, OPC_CMPDB, CMPI_EQ, RES_ALS_0134,
                  emit_src1(as, E2K_REG, type),
                  emit_src2(as, E2K_CONST, k),
                  emit_pdst(as, E2K_REG_PRED, pred));
      as->mcp = emit_bundle_finalize(as, as->mcp);
    } else if (ir->op2 & IRSLOAD_KEYINDEX) {
      NIY
    } else {
      /*
        ldd base, ofs, dest
        sard   dest, 47, type
        cmpesb type, LJ_TYPE, predN
        asm_guard(inverted);
      */
      intptr_t k = irt_isnum(t) ? (int32_t)LJ_TISNUM :
                   (int32_t)irt_toitype(t);
      opce = irt_isnum(t) ? CMPI_B : CMPI_EQ;
      asm_guard(as, pred, 1);
      emit_alopf7(as, 0, OPC_CMPSB, opce, RES_ALS_0134,
                  emit_src1(as, E2K_REG, type),
                  emit_src2(as, E2K_CONST, k),
                  emit_pdst(as, E2K_REG_PRED, pred));
      as->mcp = emit_bundle_finalize(as, as->mcp);

      emit_alopf1(as, 0, OPC_SARD, RES_ALS_012345,
                  emit_src1(as, E2K_REG, dest),
                  emit_src2(as, E2K_CONST, 47),
                  emit_dst(as, E2K_REG, type));
      as->mcp = emit_bundle_finalize(as, as->mcp);
    }
    cop = OPC_LDD;
  } else {
    cop = irt_isint(t) ? OPC_LDW : OPC_LDD;
  }
  emit_alopf1(as, 0, cop, RES_ALS_0235,
              emit_src1(as, E2K_REG, base),
              emit_src2(as, E2K_CONST, ofs),
              emit_dst(as, E2K_REG, dest));
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

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
  emit_alopf3(as, 0, OPC_STD, RES_ALS_25,
              emit_src1(as, E2K_REG, tab),
              emit_src2(as, E2K_CONST, offsetof(GCtab, gclist)),
              emit_src3(as, E2K_REG, link));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  emit_alopf3(as, 0, OPC_STB, RES_ALS_25,
              emit_src1(as, E2K_REG, tab),
              emit_src2(as, E2K_CONST, offsetof(GCtab, marked)),
              emit_src3(as, E2K_REG, mark));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  emit_setgl(as, tab, gc.grayagain);
  emit_getgl(as, link, gc.grayagain);
  /* Clear black bit. */
  emit_alopf1(as, 0, OPC_XORD, RES_ALS_012345,
                emit_src1(as, E2K_REG, tmp),
                emit_src2(as, E2K_REG, mark),
                emit_dst(as, E2K_REG, mark));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  Reg pred = ra_pred(as, RSET_PRED);
  emit_ibranch(as, (ptrdiff_t)((void *)l_end - (void *)as->mcp), pred, 0);
  as->mcp = emit_bundle_finalize(as, as->mcp);
  emit_alopf7(as, 0, OPC_CMPDB, CMPI_EQ, RES_ALS_0134,
              emit_src1(as, E2K_REG, tmp),
              emit_src2(as, E2K_CONST, 0),
              emit_pdst(as, E2K_REG_PRED, pred));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  emit_alopf1(as, 0, OPC_ANDD, RES_ALS_012345,
              emit_src1(as, E2K_REG, mark),
              emit_src2(as, E2K_CONST, LJ_GC_BLACK),
              emit_dst(as, E2K_REG, tmp));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  emit_alopf1(as, 0, OPC_LDB, RES_ALS_0235,
              emit_src1(as, E2K_REG, tab),
              emit_src2(as, E2K_CONST, offsetof(GCtab, marked)),
              emit_dst(as, E2K_REG, mark));
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

/* -- FP/int arithmetic and logic operations ------------------------------ */

static void asm_alopf1(ASMState *as, IRIns *ir, int cop, int mask)
{
  RegSet allow = RSET_GPR;
  Reg dest = ra_dest(as, ir, allow);
  Reg left = ra_hintalloc(as, ir->op1, dest, allow);
  allow = rset_exclude(allow, left);
  uint32_t right_src2 = 0;
  if (irref_isk(ir->op2)) {
    intptr_t k = get_kval(as, ir->op2);
    right_src2 = emit_src2(as, E2K_CONST, k);
  } else {
    Reg right = ra_alloc1(as, ir->op2, allow);
    allow = rset_exclude(allow, right);
    right_src2 = emit_src2(as, E2K_REG, right);
  }

  if (irt_isguard(ir->t)) { /* For IR_ADDOV etc. */
    lj_assertA(!irt_is64(ir->t), "bad usage");
    Reg tmp1 = ra_scratch(as, allow);
    Reg tmp2 = ra_scratch(as, rset_exclude(allow, tmp1));
    Reg pred = ra_pred(as, RSET_PRED);
    asm_guard(as, pred, 0);
    /* ((dest^left) & (dest^(~)right)) < 0 */
    emit_alopf7(as, 0, OPC_CMPSB, CMPI_LT, RES_ALS_0134,
                emit_src1(as, E2K_REG, tmp1),
                emit_src2(as, E2K_CONST, 0),
                emit_pdst(as, E2K_REG_PRED, pred));
    as->mcp = emit_bundle_finalize(as, as->mcp);
    emit_alopf1(as, 0, OPC_ANDS, RES_ALS_012345,
                emit_src1(as, E2K_REG, tmp1),
                emit_src2(as, E2K_REG, tmp2),
                emit_dst(as, E2K_REG, tmp1));
    as->mcp = emit_bundle_finalize(as, as->mcp);
    emit_alopf1(as, 0, OPC_XORS, RES_ALS_012345,
                  emit_src1(as, E2K_REG, dest),
                  emit_src2(as, E2K_REG, left),
                  emit_dst(as, E2K_REG, tmp1));
    emit_alopf1(as, 0, ir->o == IR_ADDOV ? OPC_XORS : OPC_XORNS,
                  RES_ALS_012345,
                  emit_src1(as, E2K_REG, dest),
                  right_src2,
                  emit_dst(as, E2K_REG, tmp2));
    as->mcp = emit_bundle_finalize(as, as->mcp);
  }

  emit_alopf1(as, 0, cop, mask,
              emit_src1(as, E2K_REG, left), right_src2,
              emit_dst(as, E2K_REG, dest));
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

static void asm_add(ASMState *as, IRIns *ir)
{
  /*
    (f)add(s/d) rN, src2, rN
  */
  asm_alopf1(as, ir,
             irt_isnum(ir->t) ? OPC_FADDD :
             (irt_is64(ir->t) ? OPC_ADDD : OPC_ADDS),
             irt_isnum(ir->t) ? RES_ALS_0134 : RES_ALS_012345);
}

static void asm_sub(ASMState *as, IRIns *ir)
{
  /*
    (f)sub(s/d) rN, src2, rN
  */
  asm_alopf1(as, ir,
             irt_isnum(ir->t) ? OPC_FSUBD :
             (irt_is64(ir->t) ? OPC_SUBD : OPC_SUBS),
             irt_isnum(ir->t) ? RES_ALS_0134 : RES_ALS_012345);
}

static void asm_mul(ASMState *as, IRIns *ir)
{
  int cop = 0, mask = 0;
  /*
    (f)mul(s/d) rN, src2, rN
  */
  if (irt_isnum(ir->t)) {
    asm_alopf1(as, ir, OPC_FMULD, RES_ALS_0134);
  } else {
    cop = irt_is64(ir->t) ? OPC_MULD : OPC_MULS;
    mask = RES_ALS_03;
    NIY
    //asm_alopf11(as, ir, cop, opce);
  }
}

#define asm_addov(as, ir) asm_alopf1(as, ir, OPC_ADDS, RES_ALS_012345)
#define asm_subov(as, ir) asm_alopf1(as, ir, OPC_SUBS, RES_ALS_012345)

/* -- Comparisons --------------------------------------------------------- */

static const uint32_t asm_compmap[IR_ABC+1] = {
  /* op     opce  */
  /* LT  */ CMPI_LT, /* inverted */
  /* GE  */ CMPI_LT,
  /* LE  */ CMPI_LE, /* inverted */
  /* GT  */ CMPI_LE,
  /* ULT */ CMPI_B,  /* inverted */
  /* UGE */ CMPI_B,
  /* ULE */ CMPI_BE, /* inverted */
  /* UGT */ CMPI_BE,
  /* EQ  */ CMPI_EQ, /* inverted */
  /* NE  */ CMPI_EQ,
  /* ABC */ CMPI_BE, /* same as UGT */
};

static const uint32_t asm_fpcompmap[IR_ABC+1] = {
  /* op     opce */
  /* LT  */ CMPF_LT,  /* inverted */
  /* GE  */ CMPF_NLT, /* inverted */
  /* LE  */ CMPF_LE,  /* inverted */
  /* GT  */ CMPF_NLE, /* inverted */
  /* ULT */ CMPF_LT,  /* inverted */
  /* UGE */ CMPF_NLT, /* inverted */
  /* ULE */ CMPF_LE,  /* inverted */
  /* UGT */ CMPF_NLE, /* inverted */
  /* EQ  */ CMPF_EQ,  /* inverted */
  /* NE  */ CMPF_EQ,  /* should be ordered */
  /* ABC */ CMPF_NLE, /* inverted */ /* same as UGT */
};

static void asm_comp(ASMState *as, IRIns *ir)
{
  IROp op = ir->o;
  int inverted = 0, cop = 0, opce = 0;
  /*
    cmp src1, src2, predN
    asm_guard(?inverted)
  */
  if (op == IR_ABC) op = IR_UGT;
  if (irt_isnum(ir->t)) {
    inverted = (op == IR_NE) ? 0 : 1;
    cop = OPC_FCMPDB; // only doubles
    opce = asm_fpcompmap[op];
  } else {
    inverted = (op&1) ? 0 : 1;
    cop = irt_is64(ir->t) ? OPC_CMPDB : OPC_CMPSB;
    opce = asm_compmap[op];
  }
  Reg pred = ra_pred(as, RSET_PRED);
  Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
  asm_guard(as, pred, inverted);

  if (irref_isk(ir->op2)) {
    intptr_t k = get_kval(as, ir->op2);
    emit_alopf7(as, 0, cop, opce, RES_ALS_0134,
                emit_src1(as, E2K_REG, left),
                emit_src2(as, E2K_CONST, k),
                emit_pdst(as, E2K_REG_PRED, pred));
  } else {
    Reg right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    emit_alopf7(as, 0, cop, opce, RES_ALS_0134,
                emit_src1(as, E2K_REG, left),
                emit_src2(as, E2K_REG, right),
                emit_pdst(as, E2K_REG_PRED, pred));
  }
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

#define asm_equal(as, ir) asm_comp(as, ir)

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
  emit_alopf7(as, 0, OPC_CMPDB, CMPI_B, RES_ALS_0134,
              emit_src1(as, E2K_REG, tmp),
              emit_src2(as, E2K_CONST, (intptr_t)(8*topslot)),
              emit_pdst(as, E2K_REG_PRED, pred));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  if (allow != RSET_EMPTY) ra_modified(as, tmp);
  emit_alopf1(as, 0, OPC_SUBD, RES_ALS_012345,
              emit_src1(as, E2K_REG, tmp),
              emit_src2(as, E2K_REG, pbase),
              emit_dst(as, E2K_REG, tmp));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  emit_alopf1(as, 0, OPC_LDD, RES_ALS_0235,
              emit_src1(as, E2K_REG, tmp),
              emit_src2(as, E2K_CONST, offsetof(lua_State, maxstack)),
              emit_dst(as, E2K_REG, tmp));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  if (pbase == RID_TMP2)
    emit_getgl(as, RID_TMP2, jit_base);
  emit_getgl(as, tmp, cur_L);
}

/* Restore Lua stack from on-trace state. */
// TODO optimize???
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
        emit_alopf3(as, 0, OPC_STD, RES_ALS_25,
                    emit_src1(as, E2K_REG, RID_BASE),
                    emit_src2(as, E2K_CONST, ofs),
                    emit_src3(as, E2K_REG, rki));
        as->mcp = emit_bundle_finalize(as, as->mcp);
      } else {
        Reg src = ra_alloc1(as, ref, allow);
        allow = rset_exclude(allow, src);
        Reg rki = ra_allock(as, kki, allow);
        allow = rset_exclude(allow, rki);
        Reg tmp = ra_scratch(as, allow);
        emit_alopf3(as, 0, OPC_STD, RES_ALS_25,
                    emit_src1(as, E2K_REG, RID_BASE),
                    emit_src2(as, E2K_CONST, ofs),
                    emit_src3(as, E2K_REG, tmp));
        as->mcp = emit_bundle_finalize(as, as->mcp);
        emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                    emit_src1(as, E2K_REG, src),
                    emit_src2(as, E2K_REG, rki),
                    emit_dst(as, E2K_REG, tmp));
        as->mcp = emit_bundle_finalize(as, as->mcp);
      }
    } else if (irt_isnum(ir->t)) {
      Reg src = ra_alloc1(as, ref, allow);
      emit_alopf3(as, 0, OPC_STD, RES_ALS_25,
                  emit_src1(as, E2K_REG, RID_BASE),
                  emit_src2(as, E2K_CONST, ofs),
                  emit_src3(as, E2K_REG, src));
      as->mcp = emit_bundle_finalize(as, as->mcp);
    } else {
      lj_assertA(irt_ispri(ir->t) || irt_isaddr(ir->t) || irt_isinteger(ir->t),
                 "store of IR type %d", irt_type(ir->t));
      if (irref_isk(ref)) {
        TValue k;
        lj_ir_kvalue(as->J->L, &k, ir);
        Reg rki = ra_allock(as, (int64_t)k.u64, allow);
        emit_alopf3(as, 0, OPC_STD, RES_ALS_25,
                    emit_src1(as, E2K_REG, RID_BASE),
                    emit_src2(as, E2K_CONST, ofs),
                    emit_src3(as, E2K_REG, rki));
        as->mcp = emit_bundle_finalize(as, as->mcp);
      } else {
        Reg src = ra_alloc1(as, ref, allow);
        allow = rset_exclude(allow, src);
        Reg type = ra_allock(as, (int64_t)irt_toitype(ir->t) << 47, allow);
        allow = rset_exclude(allow, type);
        Reg tmp = ra_scratch(as, allow);
        emit_alopf3(as, 0, OPC_STD, RES_ALS_25,
                    emit_src1(as, E2K_REG, RID_BASE),
                    emit_src2(as, E2K_CONST, ofs),
                    emit_src3(as, E2K_REG, tmp));
        as->mcp = emit_bundle_finalize(as, as->mcp);
        if (irt_isinteger(ir->t)) {
          emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                      emit_src1(as, E2K_REG, tmp),
                      emit_src2(as, E2K_REG, type),
                      emit_dst(as, E2K_REG, tmp));
          as->mcp = emit_bundle_finalize(as, as->mcp);
          emit_alopf1(as, 0, OPC_SXT, RES_ALS_012345,
                      emit_src1(as, E2K_CONST, SXT_WZ),
                      emit_src2(as, E2K_REG, src),
                      emit_dst(as, E2K_REG, tmp));
          as->mcp = emit_bundle_finalize(as, as->mcp);
        } else {
          emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                      emit_src1(as, E2K_REG, src),
                      emit_src2(as, E2K_REG, type),
                      emit_dst(as, E2K_REG, tmp));
          as->mcp = emit_bundle_finalize(as, as->mcp);
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
  emit_alopf7(as, 0, OPC_CMPDB, CMPI_EQ, RES_ALS_0134,
              emit_src1(as, E2K_REG, RID_RET),
              emit_src2(as, E2K_CONST, 0),
              emit_pdst(as, E2K_REG_PRED, pred));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  args[0] = ASMREF_TMP1;  /* global_State *g */
  args[1] = ASMREF_TMP2;  /* MSize steps     */
  asm_gencall(as, ci, args);
  tmp1 = ra_releasetmp(as, ASMREF_TMP1);
  emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
              emit_src1(as, E2K_REG, RID_DISPATCH),
              emit_src2(as, E2K_CONST, GG_DISP2G),
              emit_dst(as, E2K_REG, tmp1));
  as->mcp = emit_bundle_finalize(as, as->mcp);
  tmp2 = ra_releasetmp(as, ASMREF_TMP2);
  emit_loadi(as, tmp2, as->gcsteps);
  /* Jump around GC step if GC total < GC threshold. */
  emit_ibranch(as, (ptrdiff_t)((void *)l_end - (void *)as->mcp), pred, 0);
  as->mcp = emit_bundle_finalize(as, as->mcp);
  emit_alopf7(as, 0, OPC_CMPDB, CMPI_B, RES_ALS_0134,
              emit_src1(as, E2K_REG, tmp1),
              emit_src2(as, E2K_REG, tmp2),
              emit_pdst(as, E2K_REG_PRED, pred));
  as->mcp = emit_bundle_finalize(as, as->mcp);
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
  } else {
    // TODO not sure about this case, need real example
    NIY
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
  /*
    getsp spadj, RID_SP(2 nop)
    ibranch lj_vm_exit_interp(lnk)
  */
  emit_ibranch(as, (ptrdiff_t)((void *)target - (void *)p), 0, 0);
  p = emit_bundle_finalize(as, p); /* 4(HS+SS+CS0+Align) */
  if (spadj) {
    emit_alopf12(as, 0, OPC_GETSP, RW_USD, OPC2_EXT, OPCE_NONE, RES_ALS0,
                 emit_src2(as, E2K_CONST, spadj),
                 emit_dst(as, E2K_REG, RID_SP));
    p = emit_bundle_finalize(as, p); /* 4(HS+ALS+ALES+LTS) */
  } else {
    p[-1] = E2K_NOP; p[-2] = E2K_NOP; p[-3] = E2K_NOP; p[-4] = E2K_NOP;
  }
}

/* Prepare tail of code. */
static void asm_tail_prep(ASMState *as)
{
  /* initialized by zero, it counts as nop */
  as->mcp = as->mctop - 8; // TODO
  as->invmcp = as->loopref ? as->mcp : NULL;
}

/* -- Trace setup --------------------------------------------------------- */

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
      if (p[1] != exitno) continue;
      /* p[-3] - E2K_NOPATCH_GC_CHECK_HS; p[-2] - E2K_NOPATCH_GC_CHECK. */
      /* p[-1] - HS; p[0] - ALS; p[1] LTS; p[2] - PDS or Align. */
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

// TODO
static void asm_fpdiv(ASMState *as, IRIns *ir)
{  NIY }

static void asm_neg(ASMState *as, IRIns *ir)
{  NIY }

static void asm_hiop(ASMState *as, IRIns *ir)
{  NIY }

static void asm_prof(ASMState *as, IRIns *ir)
{  NIY }

static void asm_bnot(ASMState *as, IRIns *ir)
{  NIY }

static void asm_bswap(ASMState *as, IRIns *ir)
{  NIY }

static void asm_band(ASMState *as, IRIns *ir)
{  NIY }

static void asm_bor(ASMState *as, IRIns *ir)
{  NIY }

static void asm_bxor(ASMState *as, IRIns *ir)
{  NIY }

static void asm_bshl(ASMState *as, IRIns *ir)
{  NIY }

static void asm_bshr(ASMState *as, IRIns *ir)
{  NIY }

static void asm_bsar(ASMState *as, IRIns *ir)
{  NIY }

static void asm_brol(ASMState *as, IRIns *ir)
{  NIY }

static void asm_bror(ASMState *as, IRIns *ir)
{  NIY }

static void asm_abs(ASMState *as, IRIns *ir)
{  NIY }

static void asm_fpmath(ASMState *as, IRIns *ir)
{  NIY }

static void asm_tobit(ASMState *as, IRIns *ir)
{  NIY }

static void asm_min(ASMState *as, IRIns *ir)
{  NIY }

static void asm_max(ASMState *as, IRIns *ir)
{  NIY }

static void asm_mulov(ASMState *as, IRIns *ir)
{  NIY }

static void asm_href(ASMState *as, IRIns *ir, IROp merge)
{  NIY }

static void asm_uref(ASMState *as, IRIns *ir)
{  NIY }

static void asm_fref(ASMState *as, IRIns *ir)
{  NIY }

static void asm_strref(ASMState *as, IRIns *ir)
{  NIY }

static void asm_xload(ASMState *as, IRIns *ir)
{  NIY }

static void asm_fstore(ASMState *as, IRIns *ir)
{  NIY }

static void asm_xstore(ASMState *as, IRIns *ir)
{  NIY }

static void asm_cnew(ASMState *as, IRIns *ir)
{  NIY }

static void asm_obar(ASMState *as, IRIns *ir)
{  NIY }

static void asm_strto(ASMState *as, IRIns *ir)
{  NIY }

static void asm_callx(ASMState *as, IRIns *ir)
{  NIY }

static Reg asm_setup_call_slots(ASMState *as, IRIns *ir, const CCallInfo *ci)
{ NIY }

static void asm_bufhdr_write(ASMState *as, Reg sb)
{ NIY }
