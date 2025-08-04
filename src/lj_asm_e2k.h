/*
** E2K IR assembler (SSA IR -> machine code).
** Copyright (C) 2005-2025 Mike Pall. See Copyright Notice in luajit.h
*/

#define NIY __builtin_trap();

/* -- Register allocator extensions --------------------------------------- */

static Reg ra_pred(ASMState *as, RegSet allow)
{
  Reg r = ra_pick(as, allow);
  ra_modified(as, r);
  RA_DBGX((as, "assign predicate    $r", r));
  return r;
}

static Reg ra_ctpr(ASMState *as, RegSet allow)
{
  Reg r = ra_pick(as, allow);
  ra_modified(as, r);
  RA_DBGX((as, "assign ctpr         $r", r));
  return r;
}

static Reg ra_gpr(ASMState *as, RegSet allow)
{
  Reg r = ra_pick(as, allow);
  ra_modified(as, r);
  RA_DBGX((as, "assign gpr          $r",  r));
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
    disp ctpr1, ->lj_vm_exit_handler
    stw STACK, STACK_TMP, TMP0
    --
    addd  0, as->T->traceno, TMP0
    ct ctpr1
    --
  */

  /* Register allocation is not started yet */
  MCode *mxp = as->mctop;
  emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                emit_src1(as, E2K_CONST, 0),
                emit_src2(as, E2K_CONST, as->T->traceno),
                emit_dst(as, E2K_REG, RID_TMP));
  emit_ct(as, RID_CTPR1, 0, 0);
  mxp = emit_bundle_finalize(as, mxp);
  emit_alopf3(as, 0, OPC_STW, RES_ALS_25,
                emit_src1(as, E2K_REG, RID_SP),
                emit_src2(as, E2K_CONST, E2K_STACK_TMP),
                emit_src3(as, E2K_REG, RID_TMP));
  emit_copf2(as, OPC_DISP, RID_CTPR1,
            (ptrdiff_t)((void *)lj_vm_exit_handler - (void *)mxp));
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
    as->mcp = p + 1;
    inverted = inverted ? 0 : 1;
    target = p; /* Patch target later in asm_loop_fixup. */
  }
  emit_alopf1(as, 0, OPC_ADDD, RES_ALS_012345,
                emit_src1(as, E2K_CONST, 0),
                emit_src2(as, E2K_CONST, as->snapno),
                emit_dst(as, E2K_REG, RID_TMP));
  p = emit_bundle_finalize(as, p);

  emit_ct(as, RID_CTPR1, pred, inverted);
  p = emit_bundle_finalize(as, p);

  emit_copf2(as, OPC_DISP, RID_CTPR1,
            (ptrdiff_t)((void *)target - (void *)p));
  /* do not finalize here */
  as->mcp = p;
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

/* -- Type conversions ---------------------------------------------------- */

static void asm_tointg(ASMState *as, IRIns *ir, Reg left)
{
  Reg pred = ra_pred(as, RSET_PRED);
  Reg tmp = ra_scratch(as, rset_exclude(RSET_GPR, left));
  Reg dest = ra_dest(as, ir, RSET_GPR);
  asm_guard(as, pred, 1);
  /*
    fdtoistr left, dest
    --
    istofd dest, tmp
    --
    fcmpeqdb left, tmp, predN
    disp ctprN, as->mctop
    --
    ct ctprN, ~predN
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
  lj_assertA(irt_type(ir->t) != st, "inconsistent types for CONV");
  Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
  if (irt_isfp(ir->t)) {
    Reg dest = ra_dest(as, ir, RSET_GPR);
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
      Reg dest = ra_dest(as, ir, RSET_GPR);
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
  }
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
  int32_t ofs = 8*((int32_t)ir->op1-2);
  IRType1 t = ir->t;
  int cop = 0, opce = 0;
  Reg dest = RID_NONE, base = RID_NONE;
  lj_assertA(!(ir->op2 & IRSLOAD_PARENT),
             "bad parent SLOAD");  /* Handled by asm_head_side(). */
  lj_assertA(irt_isguard(ir->t) || !(ir->op2 & IRSLOAD_TYPECHECK),
             "inconsistent SLOAD variant");
  if ((ir->op2 & IRSLOAD_CONVERT) && irt_isguard(t) && irt_isint(t)) {
    dest = ra_scratch(as, RSET_GPR);
    asm_tointg(as, ir, dest);
    base = ra_alloc1(as, REF_BASE, RSET_GPR);
    t.irt = IRT_NUM; /* Continue with a regular number type check. */
  } else if (ra_used(ir)) {
    lj_assertA(irt_isnum(ir->t) || irt_isint(ir->t) || irt_isaddr(ir->t),
               "bad SLOAD type %d", irt_type(t));
    dest = ra_dest(as, ir, RSET_GPR);
    base = ra_alloc1(as, REF_BASE, RSET_GPR);
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
  } else {
    if (!(ir->op2 & IRSLOAD_TYPECHECK))
      return; /* No type check: avoid base alloc. */
    base = ra_alloc1(as, REF_BASE, RSET_GPR);
  }
  if (ir->op2 & IRSLOAD_TYPECHECK) {
    Reg type = ra_scratch(as, rset_exclude(RSET_GPR, dest));
    Reg pred = ra_pred(as, RSET_PRED);
    if (irt_ispri(t)) {
      NIY
    } else if (ir->op2 & IRSLOAD_KEYINDEX) {
      NIY
    } else {
      intptr_t k = irt_isnum(t) ? (int32_t)LJ_TISNUM :
                   (int32_t)irt_toitype(t);
      opce = irt_isnum(t) ? CMPI_B : CMPI_EQ;
      asm_guard(as, pred, 1);
      /*
        ld(s/d) base, ofs, dest
        --
        sard   dest, 47, type
        --
        cmpesb type, LJ_TYPE, predN
        disp ctprN, as->mctop
        --
        ct ctprN, ~predN
      */
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

/* -- FP/int arithmetic and logic operations ------------------------------ */

static void asm_alopf1(ASMState *as, IRIns *ir, int cop, int mask)
{
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
  if (irref_isk(ir->op2)) {
    intptr_t k = get_kval(as, ir->op2);
    emit_alopf1(as, 0, cop, mask,
                emit_src1(as, E2K_REG, left),
                emit_src2(as, E2K_CONST, k),
                emit_dst(as, E2K_REG, dest));
  } else {
    Reg right = ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left));
    emit_alopf1(as, 0, cop, mask,
                emit_src1(as, E2K_REG, left),
                emit_src2(as, E2K_REG, right),
                emit_dst(as, E2K_REG, dest));
  }
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

static void asm_add(ASMState *as, IRIns *ir)
{
  /*
    (f)add(s/d) rN, src2, rN
  */
  int cop = 0, mask = 0;
  if (irt_isnum(ir->t)) {
    cop = OPC_FADDD; // only doubles
    mask = RES_ALS_0134;
  } else {
    cop = irt_is64(ir->t) ? OPC_ADDD : OPC_ADDS;
    mask = RES_ALS_012345;
  }
  asm_alopf1(as, ir, cop, mask);
}

static void asm_sub(ASMState *as, IRIns *ir)
{
  /*
    (f)add(s/d) rN, src2, rN
  */
  int cop = 0, mask = 0;
  if (irt_isnum(ir->t)) {
    cop = OPC_FSUBD; // only doubles
    mask = RES_ALS_0134;
  } else {
    cop = irt_is64(ir->t) ? OPC_SUBD : OPC_SUBS;
    mask = RES_ALS_012345;
  }
  asm_alopf1(as, ir, cop, mask);
}

static void asm_mul(ASMState *as, IRIns *ir)
{
  int cop = 0, mask = 0;
  /*
    (f)mul(s/d) rN, src2, rN
  */
  if (irt_isnum(ir->t)) {
    cop = OPC_FMULD; // only doubles
    mask = RES_ALS_0134;
    asm_alopf1(as, ir, cop, mask);
  } else {
    cop = irt_is64(ir->t) ? OPC_MULD : OPC_MULS;
    mask = RES_ALS_03;
    NIY
    //asm_alopf11(as, ir, cop, opce);
  }
}

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
    disp ctprN, stub(patch) or to mctop
    cmp src1, src2, predN
    --
    addd  0, as->snapno, TMP0
    ct ctprN, predN (inverted)
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

/* Restore Lua stack from on-trace state. */
// TODO optimize???
static void asm_stack_restore(ASMState *as, SnapShot *snap)
{
  RegSet allow = RSET_GPR;
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
  lj_assertA(map + nent == flinks, "inconsistent frames in snapshot");
}

/* -- Loop handling ------------------------------------------------------- */

static void asm_loop_fixup(ASMState *as)
{
  MCode *p = as->mctop;
  MCode *target = as->mcp;
  /* p[-8] - HS; p[-7] - ALS(cmp); p[-6] - CS0 */
  if (as->loopinv) { /* Inverted loop branch? */
    /* asm_guard already inverted the cond branch. Only patch the target. */
    uint32_t tmp = p[-6] & 0xf0000000;
    uint32_t disp = (ptrdiff_t)((void *)target - (void *)p + 4*8) >> 3;
    p[-6] = tmp | (disp & 0xfffffff);
  } else {
    // TODO not sure about this case, need real example
    NIY
  }
}

static void asm_loop_tail_fixup(ASMState *as)
{
  UNUSED(as); /* Nothing to do. */
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

/* Prepare tail of code. */
static void asm_tail_prep(ASMState *as)
{
  // TODO leave space for branch ??
  // as->mcp =  as->mctop - N;
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

// TODO
static void asm_fpdiv(ASMState *as, IRIns *ir)
{  NIY }

static void asm_neg(ASMState *as, IRIns *ir)
{  NIY }

static void asm_hiop(ASMState *as, IRIns *ir)
{  NIY }

static void asm_prof(ASMState *as, IRIns *ir)
{  NIY }

static void asm_retf(ASMState *as, IRIns *ir)
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

static void asm_addov(ASMState *as, IRIns *ir)
{  NIY }

static void asm_subov(ASMState *as, IRIns *ir)
{  NIY }

static void asm_mulov(ASMState *as, IRIns *ir)
{  NIY }

static void asm_href(ASMState *as, IRIns *ir, IROp merge)
{  NIY }

static void asm_uref(ASMState *as, IRIns *ir)
{  NIY }

static void asm_hrefk(ASMState *as, IRIns *ir)
{  NIY }

static void asm_fref(ASMState *as, IRIns *ir)
{  NIY }

static void asm_strref(ASMState *as, IRIns *ir)
{  NIY }

static void asm_ahuvload(ASMState *as, IRIns *ir)
{  NIY }

static void asm_xload(ASMState *as, IRIns *ir)
{  NIY }

static void asm_fstore(ASMState *as, IRIns *ir)
{  NIY }

static void asm_xstore(ASMState *as, IRIns *ir)
{  NIY }

static void asm_cnew(ASMState *as, IRIns *ir)
{  NIY }

static void asm_tbar(ASMState *as, IRIns *ir)
{  NIY }

static void asm_obar(ASMState *as, IRIns *ir)
{  NIY }

static void asm_strto(ASMState *as, IRIns *ir)
{  NIY }

static void asm_callx(ASMState *as, IRIns *ir)
{  NIY }

static void asm_stack_check(ASMState *as, BCReg topslot,
          IRIns *irp, RegSet allow, ExitNo exitno)
{ NIY }

static Reg asm_setup_call_slots(ASMState *as, IRIns *ir, const CCallInfo *ci)
{ NIY }

static void asm_tail_fixup(ASMState *as, TraceNo lnk)
{ NIY }

static void asm_gencall(ASMState *as, const CCallInfo *ci, IRRef *args)
{ NIY }

static void asm_setupresult(ASMState *as, IRIns *ir, const CCallInfo *ci)
{ NIY }

static void asm_gc_check(ASMState *as)
{ NIY }

static void asm_tvptr(ASMState *as, Reg dest, IRRef ref, MSize mode)
{ NIY }

static void asm_bufhdr_write(ASMState *as, Reg sb)
{ NIY }

void lj_asm_patchexit(jit_State *J, GCtrace *T, ExitNo exitno, MCode *target)
{ NIY }
