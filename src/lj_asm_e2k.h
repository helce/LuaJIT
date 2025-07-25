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
  //E2K_NOP(as, E2K_NOP_DISP_CT);
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
  //E2K_NOP(as, E2K_NOP_DISP_CT);
  /* do not finalize here */
  as->mcp = p;
}

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

static void asm_sub(ASMState *as, IRIns *ir)
{  NIY }

static void asm_mul(ASMState *as, IRIns *ir)
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

static void asm_sload(ASMState *as, IRIns *ir)
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

static void asm_conv(ASMState *as, IRIns *ir)
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

static void asm_loop_fixup(ASMState *as)
{ NIY }

void lj_asm_patchexit(jit_State *J, GCtrace *T, ExitNo exitno, MCode *target)
{ NIY }

/* -- FP/int arithmetic and logic operations ------------------------------ */

static void asm_add(ASMState *as, IRIns *ir)
{
  IRType1 t = ir->t;
  E2kOperand op1, op2, op3;
  int cop = 0;
  /*
    (f)add(s/d) rN, src2, rN
  */
  if (irt_isnum(t)) {
    cop = OPC_FADDD; // only doubles
    //E2K_NOP(as, E2K_NOP_OUT4F);
  } else {
    cop = irt_is64(t) ? OPC_ADDD : OPC_ADDS;
  }

  Reg dest = ra_dest(as, ir, RSET_GPR);
  Reg left = ra_hintalloc(as, ir->op1, dest, RSET_GPR);
  E2K_REG(REG_R, left, op1);
  if (irref_isk(ir->op2)) {
    op2 = get_kval(as, ir->op2);
  } else {
    E2K_REG(REG_R, ra_alloc1(as, ir->op2, rset_exclude(RSET_GPR, left)), op2);
  }
  E2K_REG(REG_R, dest, op3);
  E2K_ALOPF1(as, 0, cop, op1, op2, op3, RES_ALS_012345);
  as->mcp = emit_bundle_finalize(as, as->mcp);
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

  E2K_ALOPF7(as, 0, cop, opce, op1, op2, pred,
             RES_ALS_0134);
  as->mcp = emit_bundle_finalize(as, as->mcp);
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
