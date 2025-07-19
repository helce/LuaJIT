/*
** E2K IR assembler (SSA IR -> machine code).
** Copyright (C) 2005-2025 Mike Pall. See Copyright Notice in luajit.h
*/

#define NIY __builtin_trap();

/* -- Register allocator extensions --------------------------------------- */

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

static void asm_comp(ASMState *as, IRIns *ir)
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

static void asm_add(ASMState *as, IRIns *ir)
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

static void asm_setup_target(ASMState *as)
{ NIY }

static void asm_tail_fixup(ASMState *as, TraceNo lnk)
{ NIY }

static void asm_tail_prep(ASMState *as)
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
