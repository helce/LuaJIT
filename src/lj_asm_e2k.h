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
  E2kOperand op1, op2, op3;

  E2K_CONST(CONST_U4, 0, op1);
  E2K_CONST(CONST_U16, as->T->traceno, op2);
  E2K_REG(REG_G, RID_TMP, op3);
  E2K_ALOPF1(as, 0, OPC_ADDD, op1, op2, op3, RES_ALS_012345);
  E2K_CT(as, RID_CTPR1, 0, 0);
  mxp = emit_bundle_finalize(as, mxp);


  E2K_REG(REG_R, RID_SP, op1);
  E2K_CONST(CONST_U16, E2K_STACK_TMP, op2);
  E2K_ALOPF3(as, 0, OPC_STW, op1, op2, op3, RES_ALS_25);
  E2K_COPF2(as, OPC_DISP, RID_CTPR1,
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
  E2kOperand op1, op2, op3;
  E2K_CONST(CONST_U4, 0, op1);
  E2K_CONST(CONST_U32, as->snapno, op2);
  E2K_REG(REG_G, RID_TMP, op3);
  E2K_ALOPF1(as, 0, OPC_ADDD, op1, op2, op3, RES_ALS_012345);
  p = emit_bundle_finalize(as, p);

  E2K_CT(as, RID_CTPR1, pred, inverted);
  p = emit_bundle_finalize(as, p);

  E2K_COPF2(as, OPC_DISP, RID_CTPR1,
            (ptrdiff_t)((void *)target - (void *)p));
  /* do not finalize here */
  as->mcp = p;
}

/* -- Type conversions ---------------------------------------------------- */

static void asm_tointg(ASMState *as, IRIns *ir, Reg left)
{
  E2kOperand op_left, op_tmp, op_dest;
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
  E2K_REG(REG_R, left, op_left);
  E2K_REG(REG_R, tmp, op_tmp);
  E2K_REG(REG_R, dest, op_dest);
  E2K_ALOPF7(as, 0, OPC_FCMPDB, CMPF_EQ, op_left, op_tmp, pred, RES_ALS_0134);
  as->mcp = emit_bundle_finalize(as, as->mcp);
  E2K_ALOPF2(as, 0, OPC_FSTOD, CO_ISTOFD, op_dest, op_tmp, RES_ALS_0134);
  as->mcp = emit_bundle_finalize(as, as->mcp);
  E2K_ALOPF2(as, 0, OPC_FDTOS, CO_FDTOISTR, op_left, op_dest, RES_ALS_0134);
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

static void asm_conv(ASMState *as, IRIns *ir)
{
  IRType st = (IRType)(ir->op2 & IRCONV_SRCMASK);
  int stfp = (st == IRT_NUM || st == IRT_FLOAT);
  int st64 = (st == IRT_I64 || st == IRT_U64 || st == IRT_P64);
  int cop = 0, opce = 0;

  lj_assertA(irt_type(ir->t) != st, "inconsistent types for CONV");
  E2kOperand op1, op2;
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
  E2K_REG(REG_R, left, op1);
  E2K_REG(REG_R, dest, op2);

  if (irt_isfp(ir->t)) {
    if (stfp) { /* FP to FP conversion */
      cop = (st == IRT_NUM ? OPC_FDTOS : OPC_FSTOD);
      opce = CO_FSTOFD; /* smae for both cop */
    } else { /* INT to FP conversion */
      cop = (st == IRT_U32 || st == IRT_INT) ?
        (irt_isnum(ir->t) ? OPC_FSTOD : OPC_FSTOS) :
        (irt_isnum(ir->t) ? OPC_FDTOD : OPC_FDTOS);
      opce = CO_ISTOFS; /* smae for all cop */
    }
    E2K_ALOPF2(as, 0, cop, opce, op1, op2, RES_ALS_0134);
  } else if (stfp) { /* FP to INT conversion */
    if (irt_isguard(ir->t)) {
      /* Checked conversions are only supported from NUM to INT */
      lj_assertA(irt_isint(ir->t) && st == IRT_NUM,
                 "bad type for checked CONV");
      //asm_tointg(as, ir);
      NIY
    } else {
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
        E2K_ALOPF2(as, 0, cop, opce, op1, op2, RES_ALS_0134);
      }
    }
  } else { /* INT to INT conversion */
    NIY
  }
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

/* -- Loads and stores ---------------------------------------------------- */

static void asm_sload(ASMState *as, IRIns *ir)
{
  int32_t ofs = 8*((int32_t)ir->op1-2);
  IRType1 t = ir->t;
  E2kOperand op_dest, op_base, op_const;
  int cop;
  Reg dest = RID_NONE, base = RID_NONE;
  lj_assertA(!(ir->op2 & IRSLOAD_PARENT),
             "bad parent SLOAD");  /* Handled by asm_head_side(). */
  lj_assertA(irt_isguard(ir->t) || !(ir->op2 & IRSLOAD_TYPECHECK),
             "inconsistent SLOAD variant");
  if ((ir->op2 & IRSLOAD_CONVERT) && irt_isguard(t) && irt_isint(t)) {
    dest = ra_scratch(as, RSET_GPR);
    asm_tointg(as, ir, dest);
    base = ra_alloc1(as, REF_BASE, RSET_GPR);
    E2K_REG(REG_R, dest, op_dest);
    t.irt = IRT_NUM; /* Continue with a regular number type check. */
  } else if (ra_used(ir)) {
    lj_assertA(irt_isnum(ir->t) || irt_isint(ir->t) || irt_isaddr(ir->t),
               "bad SLOAD type %d", irt_type(t));
    dest = ra_dest(as, ir, RSET_GPR);
    base = ra_alloc1(as, REF_BASE, RSET_GPR);
    E2K_REG(REG_R, dest, op_dest);
    if (ir->op2 & IRSLOAD_CONVERT) {
      if (irt_isint(t)) {
        E2K_ALOPF2(as, 0, OPC_FDTOS, CO_FDTOISTR, op_dest, op_dest, RES_ALS_0134);
        as->mcp = emit_bundle_finalize(as, as->mcp);
        t.irt = IRT_NUM;
      } else {
        E2K_ALOPF2(as, 0, OPC_FSTOD, CO_ISTOFD, op_dest, op_dest, RES_ALS_0134);
        as->mcp = emit_bundle_finalize(as, as->mcp);
        t.irt = IRT_INT;
      }
    } else if (irt_isaddr(t)) {
      /* Clear type from pointers. */
      // TODO EXTRACT TYPE 
      NIY
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
    E2kOperand op_type;
    E2K_REG(REG_R, type, op_type);
    Reg pred = ra_pred(as, RSET_PRED);
    if (irt_ispri(t)) {
      NIY
    } else if (ir->op2 & IRSLOAD_KEYINDEX) {
      NIY
    } else {
      E2K_CONST(CONST_U32, (int32_t)irt_toitype(t), op_const);
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
      E2K_ALOPF7(as, 0, OPC_CMPSB, CMPI_EQ, op_type, op_const, pred, RES_ALS_0134);
      as->mcp = emit_bundle_finalize(as, as->mcp);
      E2K_CONST(CONST_U16, 47, op_const);
      E2K_ALOPF1(as, 0, OPC_SARD, op_dest, op_const, op_type, RES_ALS_012345);
      as->mcp = emit_bundle_finalize(as, as->mcp);
    }
    cop = OPC_LDD;
  } else {
    cop = irt_isint(t) ? OPC_LDW : OPC_LDD;
  }
  E2K_CONST(CONST_U32, ofs, op_const);
  E2K_REG(REG_R, base, op_base);
  E2K_ALOPF1(as, 0, cop, op_base, op_const, op_dest, RES_ALS_0235);
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

/* -- FP/int arithmetic and logic operations ------------------------------ */

static void asm_alopf1(ASMState *as, IRIns *ir, int cop, int mask)
{
  E2kOperand op1, op2, op3;
  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
  E2K_REG(REG_R, left, op1);
  if (irref_isk(ir->op2)) {
    op2 = get_kval(as, ir->op2);
  } else {
    E2K_REG(REG_R, ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left)), op2);
  }
  E2K_REG(REG_R, dest, op3);
  E2K_ALOPF1(as, 0, cop, op1, op2, op3, mask);
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
  /* LT  */ CMPI_LT,
  /* GE  */ CMPI_LT, /* inverted */
  /* LE  */ CMPI_LE,
  /* GT  */ CMPI_LE, /* inverted */
  /* ULT */ CMPI_B,
  /* UGE */ CMPI_B,  /* inverted */
  /* ULE */ CMPI_BE,
  /* UGT */ CMPI_BE, /* inverted */
  /* EQ  */ CMPI_EQ,
  /* NE  */ CMPI_EQ, /* inverted */
  /* ABC */ CMPI_BE, /* inverted */  /* same as UGT */
};

static const uint32_t asm_fpcompmap[IR_ABC+1] = {
  /* op     opce */
  /* LT  */ CMPF_LT,
  /* GE  */ CMPF_NLT,
  /* LE  */ CMPF_LE,
  /* GT  */ CMPF_NLE,
  /* ULT */ CMPF_LT,
  /* UGE */ CMPF_NLT,
  /* ULE */ CMPF_LE,
  /* UGT */ CMPF_NLE,
  /* EQ  */ CMPF_EQ,
  /* NE  */ CMPF_EQ, /* inverted, should be ordered */
  /* ABC */ CMPF_NLE, /* same as UGT */
};

static void asm_comp(ASMState *as, IRIns *ir)
{
  IROp op = ir->o;
  RA_DBG_FLUSH();
  E2kOperand op1, op2;
  int inverted = 0, cop = 0, opce = 0;
  /*
    disp ctprN, stub(patch) or to mctop
    cmp src1, src2, predN
    --
    addd  0, as->snapno, TMP0
    ct ctprN, predN (inverted)
  */
  if (op == IR_ABC) op = IR_UGT;
  Reg pred = ra_pred(as, RSET_PRED);

  if (irt_isnum(ir->t)) {
    inverted = (op == IR_NE) ? 1 : 0;
    cop = OPC_FCMPDB; // only doubles
    opce = asm_fpcompmap[op];
  } else {
    inverted = (op&1) ? 1 : 0;
    cop = irt_is64(ir->t) ? OPC_CMPDB : OPC_CMPSB;
    opce = asm_compmap[op];
  }

  asm_guard(as, pred, inverted);

  Reg left = ra_alloc1(as, ir->op1, RSET_GPR);
  E2K_REG(REG_R, left, op1);

  if (irref_isk(ir->op2)) {
    op2 = get_kval(as, ir->op2);
  } else {
    E2K_REG(REG_R, ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left)), op2);
  }

  E2K_ALOPF7(as, 0, cop, opce, op1, op2, pred, RES_ALS_0134);
  as->mcp = emit_bundle_finalize(as, as->mcp);
}

/* -- Loop handling ------------------------------------------------------- */

static void asm_loop_fixup(ASMState *as)
{
  MCode *p = as->mctop;
  MCode *target = as->mcp;
  /* p[-10] - HS; p[-9] - ALS(cmp); p[-8] - CS0 */
  uint32_t tmp = p[-8] & 0xf0000000;
  uint32_t disp = (target - p + 8) >> 3;
  p[-8] = tmp | (disp & 0xfffffff);
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

static void asm_equal(ASMState *as, IRIns *ir)
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

static void asm_aref(ASMState *as, IRIns *ir)
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

static void asm_fload(ASMState *as, IRIns *ir)
{  NIY }

static void asm_xload(ASMState *as, IRIns *ir)
{  NIY }

static void asm_ahustore(ASMState *as, IRIns *ir)
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

static void asm_head_root_base(ASMState *as)
{  NIY }

static Reg asm_head_side_base(ASMState *as, IRIns *irp)
{
  NIY
  return 0;
}

static void asm_stack_restore(ASMState *as, SnapShot *snap)
{  NIY }

static void asm_stack_check(ASMState *as, BCReg topslot,
          IRIns *irp, RegSet allow, ExitNo exitno)
{ NIY }

static Reg asm_setup_call_slots(ASMState *as, IRIns *ir, const CCallInfo *ci)
{ NIY }

static void asm_tail_fixup(ASMState *as, TraceNo lnk)
{ NIY }

static void asm_loop_tail_fixup(ASMState *as)
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
