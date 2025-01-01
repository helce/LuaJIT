------------------------------------------------------------------------------
-- DynASM e2k module.
--
-- Copyright (C) 2005-2016 Mike Pall. All rights reserved.
-- See dynasm.lua for full copyright notice.
------------------------------------------------------------------------------

-- Module information:
local _info = {
  arch =        "e2k",
  description = "DynASM E2K module",
  version =     "1.5.0",
  vernum =      10500,
  release =     "2021-01-01",
  author =      "Svyatoslav Stupak",
  license =     "MIT",
}

-- Exported glue functions for the arch-specific module.
local _M = { _info = _info }

-- Cache library functions.
local type, tonumber, pairs, ipairs = type, tonumber, pairs, ipairs
local assert, setmetatable = assert, setmetatable
local _s = string
local sub, format, byte, char = _s.sub, _s.format, _s.byte, _s.char
local match, gmatch = _s.match, _s.gmatch
local concat, sort = table.concat, table.sort
local bit = bit or require("bit")
local band, bor, shl, sar, tohex, bswap = bit.band, bit.bor, bit.lshift, bit.arshift, bit.tohex, bit.bswap

-- Inherited tables and callbacks.
local g_opt, g_arch
local wline, werror, wfatal, wwarn

-- Action name list.
-- CHECK: Keep this in sync with the C code!
local action_names = {
  "STOP", "SECTION", "ESC", "REL_EXT",
  "REL_LG", "LABEL_LG", "REL_PC",
  "LABEL_PC", "IMM",
}

-- Maximum number of section buffer positions for dasm_put().
-- CHECK: Keep this in sync with the C code!
local maxsecpos = 25 -- Keep this low, to avoid excessively long C lines.

-- Action name -> action number.
local map_action = {}
for n,name in ipairs(action_names) do
  map_action[name] = n - 1
end

-- Action list buffer.
local actlist = {}

-- Argument list for next dasm_put(). Start with offset 0 into action list.
local actargs = { 0 }

-- Current number of section buffer positions for dasm_put().
local secpos = 1

-- Current wide instruction capture.
local wide_capture = false

-- Current wide instruction.
local wide_instr = {}

-- Current bundling mode.
local wide_mode = true

------------------------------------------------------------------------------

-- Dump action names and numbers.
local function dumpactions(out)
  out:write("DynASM encoding engine action codes:\n")
  for n,name in ipairs(action_names) do
    local num = map_action[name]
    out:write(format("  %-10s %02X  %d\n", name, num, num))
  end
  out:write("\n")
end

-- Write action list buffer as a huge static C array.
local function writeactions(out, name)
  local nn = #actlist
  local last = actlist[nn] or map_action.STOP
  actlist[nn] = nil -- Remove last word
  if nn == 0 then nn = 1 end
  out:write("static const unsigned int ", name, "[", nn, "] = {\n")
  local s = "  "
  for n,b in ipairs(actlist) do
    s = s.."0x"..tohex(b)..","
    if #s >= 75 then
      assert(out:write(s, "\n"))
      s = "  "
    end
  end
  out:write(s, "0x"..tohex(last), "\n};\n\n") -- Add last word back 
end

------------------------------------------------------------------------------

-- Add word to action list.
local function wputxw(n)
  actlist[#actlist+1] = n
end

-- Add action to list with optional arg. Advance buffer pos, too.
local function waction(action, val, name, ofs_e, ofs_s, spos)
  local w = assert(map_action[action], "bad action name `"..action.."'")
  if val then assert(val < 4095, "Too hi val {"..val.."} for action `"..action.."`") end
  wputxw(0xff000000 + w * 0x100000 + (ofs_e or 0)*0x10000 + (ofs_s or 0)*0x1000 + (val or 0))
  if name then actargs[#actargs+1] = name end
  if name or spos then secpos = secpos + (spos or 1) end
end

-- Flush action list (intervening C code or buffer pos overflow).
local function wflush(term)
  if #actlist == actargs[1] then return end -- Nothing to flush.
  if not term then waction("STOP") end -- Terminate action list.
  wline(format("dasm_put(Dst, %s);", concat(actargs, ", ")), true)
  actargs = { #actlist } -- Actionlist offset is 1st arg to next dasm_put().
  secpos = 1 -- The actionlist offset occupies a buffer position, too.
end

------------------------------------------------------------------------------

-- Global label name -> global label number. With auto assignment on 1st use.
local next_global = 20
local map_global = setmetatable({}, { __index = function(t, name)
  if not match(name, "^[%a_][%w_]*$") then werror("bad global label") end
  local n = next_global
  if n > 2047 then werror("too many global labels") end
  next_global = n + 1
  t[name] = n
  return n
end})

-- Dump global labels.
local function dumpglobals(out, lvl)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("Global labels:\n")
  for i=20,next_global-1 do
    out:write(format("  %s\n", t[i]))
  end
  out:write("\n")
end

-- Write global label enum.
local function writeglobals(out, prefix)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("enum {\n")
  for i=20,next_global-1 do
    out:write("  ", prefix, t[i], ",\n")
  end
  out:write("  ", prefix, "_MAX\n};\n")
end

-- Write global label names.
local function writeglobalnames(out, name)
  local t = {}
  for name, n in pairs(map_global) do t[n] = name end
  out:write("static const char *const ", name, "[] = {\n")
  for i=20,next_global-1 do
    out:write("  \"", t[i], "\",\n")
  end
  out:write("  (const char *)0\n};\n")
end

------------------------------------------------------------------------------

-- Extern label name -> extern label number. With auto assignment on 1st use.
local next_extern = 0
local map_extern_ = {}
local map_extern = setmetatable({}, { __index = function(t, name)
  -- No restrictions on the name for now.
  local n = next_extern
  if n > 2047 then werror("too many extern labels") end
  next_extern = n + 1
  t[name] = n
  map_extern_[n] = name
  return n
end})

-- Dump extern labels.
local function dumpexterns(out, lvl)
  out:write("Extern labels:\n")
  for i=0,next_extern-1 do
    out:write(format("  %s\n", map_extern_[i]))
  end
  out:write("\n")
end

-- Write extern label names.
local function writeexternnames(out, name)
  out:write("static const char *const ", name, "[] = {\n")
  for i=0,next_extern-1 do
    out:write("  \"", map_extern_[i], "\",\n")
  end
  out:write("  (const char *)0\n};\n")
end

------------------------------------------------------------------------------

-- Arch specific maps.
local map_archdef = {}  -- Ext. register name -> int. name.
local map_type = {}     -- Type name -> { ctype, reg }
local ctypenum = 0      -- Type number (for Dt... macros).
local rreg_list = {}    -- Rregs
local breg_list = {}    -- Bregs
local pred_list = {}    -- Predicates
local ipred_list = {}   -- Inversed predicates
local lpred_list = {}   -- Local predicates
local lipred_list = {}  -- Inversed local predicates
local ctpr_list = {}    -- Ctprs
local greg_list = {}    -- Gregs

-- Helper function to fill register maps.
local function mkrmap(reg_type, reg_num)
  for n = 0,reg_num do
    if reg_type == "RREG" then
      rreg_list["r"..n] = n
    elseif reg_type == "BREG" then
      breg_list["b"..n] = n
    elseif reg_type == "GREG" then
      greg_list["g"..n] = n
    elseif reg_type == "PRED" then
      pred_list["pred"..n] = n
    elseif reg_type == "IPRED" then
      ipred_list["~pred"..n] = n
    elseif reg_type == "LPRED" then
      lpred_list["p"..n] = n
    elseif reg_type == "LIPRED" then
      lipred_list["~p"..n] = n
    elseif reg_type == "CTPR" then
      ctpr_list["ctpr"..(n+1)] = n + 1
    end
  end
end

mkrmap("RREG", 63)
mkrmap("BREG", 127)
mkrmap("GREG", 31)
mkrmap("PRED", 31)
mkrmap("IPRED", 31)
mkrmap("LPRED", 6)
mkrmap("LIPRED", 6)
mkrmap("CTPR", 2)

-- Reverse defines for registers.
function _M.revdef(s)
  return s
end

------------------------------------------------------------------------------

-- Template strings for E2K instructions.
local map_op = {
  -- C.2.1.1 Addition/substraction/reverse substraction operations
  adds_4 = "ALU2_ALOPF1_0_0x3f_0x10",
  adds_5 = "ALU2PR_ALOPF1_0_0x3f_0x10",
  addd_4 = "ALU2_ALOPF1_0_0x3f_0x11",
  adddsm_4 = "ALU2_ALOPF1_1_0x3f_0x11",
  addd_5 = "ALU2PR_ALOPF1_0_0x3f_0x11",
  subs_4 = "ALU2_ALOPF1_0_0x3f_0x12",
  subs_5 = "ALU2PR_ALOPF1_0_0x3f_0x12",
  subd_4 = "ALU2_ALOPF1_0_0x3f_0x13",
  subdsm_4 = "ALU2_ALOPF1_1_0x3f_0x13",
  subd_5 = "ALU2PR_ALOPF1_0_0x3f_0x13",
  -- C.2.1.2 Multiplication operations
  smulx_4 = "ALU2_ALOPF11_0_0x1b_0x23_N_0x01_0xc0",
  -- C.2.2. Comparaion of integer numbers operations
  cmpbsb_4 = "ALU2_ALOPF7_0_0x1b_0x20_0x1",
  cmpbsbsm_4 = "ALU2_ALOPF7_1_0x1b_0x20_0x1",
  cmpbdb_4 = "ALU2_ALOPF7_0_0x1b_0x21_0x1",
  cmpbdbsm_4 = "ALU2_ALOPF7_1_0x1b_0x21_0x1",
  cmpesb_4 = "ALU2_ALOPF7_0_0x1b_0x20_0x2",
  cmpesbsm_4 = "ALU2_ALOPF7_1_0x1b_0x20_0x2",
  cmpedb_4 = "ALU2_ALOPF7_0_0x1b_0x21_0x2",
  cmpedbsm_4 = "ALU2_ALOPF7_1_0x1b_0x21_0x2",
  cmpbesb_4 = "ALU2_ALOPF7_0_0x1b_0x20_0x3",
  cmpbedb_4 = "ALU2_ALOPF7_0_0x1b_0x21_0x3",
  cmpbedbsm_4 = "ALU2_ALOPF7_1_0x1b_0x21_0x3",
  cmplsb_4 = "ALU2_ALOPF7_0_0x1b_0x20_0x6",
  cmplsbsm_4 = "ALU2_ALOPF7_1_0x1b_0x20_0x6",
  cmpldb_4 = "ALU2_ALOPF7_0_0x1b_0x21_0x6",
  cmplesb_4 = "ALU2_ALOPF7_0_0x1b_0x20_0x7",
  cmpledb_4 = "ALU2_ALOPF7_0_0x1b_0x21_0x7",
  cmpandesb_4 = "ALU2_ALOPF7_0_0x1b_0x22_0x2",
  cmpandedb_4 = "ALU2_ALOPF7_0_0x1b_0x23_0x2",
  cmpandedbsm_4 = "ALU2_ALOPF7_1_0x1b_0x23_0x2",
  -- C.2.4 Logical bitwise operations
  ands_4 = "ALU2_ALOPF1_0_0x3f_0x0",
  ands_5 = "ALU2PR_ALOPF1_0_0x3f_0x0",
  andd_4 = "ALU2_ALOPF1_0_0x3f_0x1",
  anddsm_4 = "ALU2_ALOPF1_1_0x3f_0x1",
  andd_5 = "ALU2PR_ALOPF1_0_0x3f_0x1",
  ors_4 = "ALU2_ALOPF1_0_0x3f_0x4",
  ord_4 = "ALU2_ALOPF1_0_0x3f_0x5",
  ord_5 = "ALU2PR_ALOPF1_0_0x3f_0x5",
  xors_4 = "ALU2_ALOPF1_0_0x3f_0x8",
  xors_5 = "ALU2PR_ALOPF1_0_0x3f_0x8",
  xord_4 = "ALU2_ALOPF1_0_0x3f_0x9",
  -- C.2.5 Shift operations
  shls_4 = "ALU2_ALOPF1_0_0x3f_0x18",
  shls_5 = "ALU2PR_ALOPF1_0_0x3f_0x18",
  shld_4 = "ALU2_ALOPF1_0_0x3f_0x19",
  shldsm_4 = "ALU2_ALOPF1_1_0x3f_0x19",
  shld_5 = "ALU2PR_ALOPF1_0_0x3f_0x19",
  shrs_4 = "ALU2_ALOPF1_0_0x3f_0x1a",
  shrd_4 = "ALU2_ALOPF1_0_0x3f_0x1b",
  shrdsm_4 = "ALU2_ALOPF1_1_0x3f_0x1b",
  shrd_5 = "ALU2PR_ALOPF1_0_0x3f_0x1b",
  scls_4 = "ALU2_ALOPF1_0_0x3f_0x14",
  scld_4 = "ALU2_ALOPF1_0_0x3f_0x15",
  scrs_4 = "ALU2_ALOPF1_0_0x3f_0x16",
  scrd_4 = "ALU2_ALOPF1_0_0x3f_0x17",
  sars_4 = "ALU2_ALOPF1_0_0x3f_0x1c",
  sard_4 = "ALU2_ALOPF1_0_0x3f_0x1d",
  sardsm_4 = "ALU2_ALOPF1_1_0x3f_0x1d",
  -- C.?.? Extract field
  getfs_4 = "ALU2_ALOPF1_0_0x3f_0x1e",
  getfs_5 = "ALU2PR_ALOPF1_0_0x3f_0x1e",
  getfssm_4 = "ALU2_ALOPF1_1_0x3f_0x1e",
  getfssm_5 = "ALU2PR_ALOPF1_1_0x3f_0x1e",
  getfd_4 = "ALU2_ALOPF1_0_0x3f_0x1f",
  getfd_5 = "ALU2PR_ALOPF1_0_0x3f_0x1f",
  getfdsm_4 = "ALU2_ALOPF1_1_0x3f_0x1f",
  getfdsm_5 = "ALU2PR_ALOPF1_1_0x3f_0x1f",
  -- C.2.7.1 Sign or zero extension
  sxt_4 = "ALU2_ALOPF1_0_0x3f_0xc",
  sxt_5 = "ALU2PR_ALOPF1_0_0x3f_0xc",
  -- C.3.2.1 FP addition and substruction operations
  faddd_4 = "ALU2_ALOPF1_0_0x1b_0x31",
  fadddsm_4 = "ALU2_ALOPF1_1_0x1b_0x31",
  fsubd_4 = "ALU2_ALOPF1_0_0x1b_0x33",
  fsubd_5 = "ALU2PR_ALOPF1_0_0x1b_0x33",
  -- C.3.2.2 Min/Max operations
  fmind_4 = "ALU2_ALOPF1_0_0x1b_0x35",
  fmaxd_4 = "ALU2_ALOPF1_0_0x1b_0x37",
  -- C.3.2.3.1 FP multiplication operations
  fmuld_4 = "ALU2_ALOPF1_0_0x1b_0x39",
  -- C.3.2.3.2 Multiplication by power of two operations
  fscales_4 = "ALU2_ALOPF11_0_0x12_0x24_N_0x01_0xc0",
  fscaled_4 = "ALU2_ALOPF11_0_0x12_0x25_N_0x01_0xc0",
  -- C.3.2.4 Division and reciprocal operations 
  fdivd_4 = "ALU2_ALOPF11_0_0x20_0x49_N_0x01_0xc0",
  -- C.3.2.5 The square root and its reciprocal operations
  fsqrtid_3 = "ALU1_ALOPF12_0_0x20_0x4d_0xc0_0x01_0xc0",
  fsqrttd_4 = "ALU2_ALOPF11_0_0x20_0x51_N_0x01_0xc0",
  -- C.3.3.3 FP comparation operations with predicate result 
  fcmpeqdb_4 = "ALU2_ALOPF7_0_0x1b_0x2f_0x0",
  fcmpltdb_4 = "ALU2_ALOPF7_0_0x1b_0x2f_0x1",
  fcmpledb_4 = "ALU2_ALOPF7_0_0x1b_0x2f_0x2",
  fcmpuoddb_4 = "ALU2_ALOPF7_0_0x1b_0x2f_0x3",
  fcmpnltdb_4 = "ALU2_ALOPF7_0_0x1b_0x2f_0x5",
  fcmpnledb_4 = "ALU2_ALOPF7_0_0x1b_0x2f_0x6",
  -- C.5.2.2 FSTOIFs and FDTOIFd operations
  fdtoifd_4 = "ALU2_ALOPF11_0_0x1b_0x6d_N_0x01_0xc0",
  -- C.5.3 Converting FP to integer operations
  fdtois_3 = "ALU1_ALOPF2_0_0x1b_0x3f_0xc0",
  fdtoid_3 = "ALU1_ALOPF2_0_0x1b_0x3d_0xc0",
  fdtoistr_3 = "ALU1_ALOPF2_0_0x1b_0x3f_0xc2",
  fdtoistr_4 = "ALU1PR_ALOPF2_0_0x1b_0x3f_0xc2",
  fdtoidtr_3 = "ALU1_ALOPF2_0_0x1b_0x3d_0xc2",
  -- C.5.4 Converting integer to FP operation
  istofd_3 = "ALU1_ALOPF2_0_0x1b_0x3e_0xc4",
  idtofd_3 = "ALU1_ALOPF2_0_0x1b_0x3d_0xc4",
  -- C.7.6 Other packed operations
  pshufb_5 = "ALU3_ALOPF21_0_0x1b_0x4d_N_0x0f_0xc0",
  -- C.10 Predicate operations
  pass_2 = "PASS",
  -- C.10.1.2 Calculation of local predicate operations
  landp_3 = "LANDP_0x1",
  -- C.11.9.1 Operations "Loading from unsaved area"
  ldb_4 = "ALU2_ALOPF1_0_0x2d_0x64",
  ldb_5 = "ALU2PR_ALOPF1_0_0x2d_0x64",
  ldbsm_4 = "ALU2_ALOPF1_1_0x2d_0x64",
  ldh_4 = "ALU2_ALOPF1_0_0x2d_0x65",
  ldw_4 = "ALU2_ALOPF1_0_0x2d_0x66",
  ldwsm_4 = "ALU2_ALOPF1_1_0x2d_0x66",
  ldw_5 = "ALU2PR_ALOPF1_0_0x2d_0x66",
  ldd_4 = "ALU2_ALOPF1_0_0x2d_0x67",
  lddsm_4 = "ALU2_ALOPF1_1_0x2d_0x67",
  ldd_5 = "ALU2PR_ALOPF1_0_0x2d_0x67",
  lddsm_5 = "ALU2PR_ALOPF1_1_0x2d_0x67",
  -- C.11.9.2 Operations "Writing to unsaved area"
  stb_4 = "ALU2_ALOPF3_0_0x24_0x24",
  stb_5 = "ALU2PR_ALOPF3_0_0x24_0x24",
  sth_4 = "ALU2_ALOPF3_0_0x24_0x25",
  stw_4 = "ALU2_ALOPF3_0_0x24_0x26",
  stw_5 = "ALU2PR_ALOPF3_0_0x24_0x26",
  std_4 = "ALU2_ALOPF3_0_0x24_0x27",
  std_5 = "ALU2PR_ALOPF3_0_0x24_0x27",
  stdsm_4 = "ALU2_ALOPF3_1_0x24_0x27",
  -- C.12.10.4 Get stack pointer operation
  getsp_3 = "ALU1_ALOPF12_0_0x01_0x58_0xec_0x01_0xc0",
  -- C.12.12 "Forward tagged value" operations
  movtd_3 = "ALU1_ALOPF2_0_0x01_0x61_0xc0",
  movtdsm_3 = "ALU1_ALOPF2_1_0x01_0x61_0xc0",
  -- C.14.2. Operations "Set registers" or "Check parameter areas"
  setwd_3 = "SETWD_0x0",
  setbn_3 = "SETBN_0x4",
  -- C.15.1. Prepare to jump on literal disp
  disp_2 = "DISP_DISP_0x0",
  -- C.15.6. Prepare to return from call
  return_1 = "DISP_RETURN_0x3",
  -- C.17.1 Transfer of control operations
  ct_2 = "CT",
  ct_1 = "CT",
  -- C.17.4 Call operations
  call_2 = "CALL_0x5",
  -- C.22.4. Push nop
  nop_1 = "NOP",
  -- Generate wide instruction
  ["--_0"] = "GEN",
}

------------------------------------------------------------------------------

local function parse_label(label, def)
  local prefix = sub(label, 1, 2)
  -- =>label (pc label reference)
  if prefix == "=>" then
    return "PC", 0, sub(label, 3)
  end
  -- ->name (global label reference)
  if prefix == "->" then
    return "LG", map_global[sub(label, 3)]
  end
  if def then
    -- [1-9] (local label definition)
    if match(label, "^[1-9]$") then
      return "LG", 10+tonumber(label)
    end
  else
    -- [<>][1-9] (local label reference)
    local dir, lnum = match(label, "^([<>])([1-9])$")
    if dir then -- Fwd: 1-9, Bkwd: 11-19.
      return "LG", lnum + (dir == ">" and 0 or 10)
    end
    -- extern label (extern label reference)
    local extname = match(label, "^extern%s+(%S+)$")
    if extname then
      return "EXT", map_extern[extname]
    end
  end
  werror("bad label `"..label.."'")
end

local function check_operand(opnd)
  local operand = {}
  if rreg_list[opnd] then
    operand = {t = "RREG", n = rreg_list[opnd]}
  elseif breg_list[opnd] then
    operand = {t = "BREG", n = breg_list[opnd]}
  elseif greg_list[opnd] then
    operand = {t = "GREG", n = greg_list[opnd]}
  elseif pred_list[opnd] then
    operand = {t = "PRED", n = pred_list[opnd]}
  elseif ipred_list[opnd] then
    operand = {t = "IPRED", n = ipred_list[opnd]}
  elseif lpred_list[opnd] then
    operand = {t = "LPRED", n = lpred_list[opnd]}
  elseif lipred_list[opnd] then
    operand = {t = "LIPRED", n = lipred_list[opnd]}
  elseif ctpr_list[opnd] then
    operand = {t = "CTPR", n = ctpr_list[opnd]}
  else
    if match(opnd, "^U64x%(.*%)$") then
      local u64 = {}
      for j in gmatch(opnd, "0x[%da-f]+") do u64[#u64 + 1] = j end
      operand = {t = "NUM_64", hi = tonumber(u64[1], 16), lo = tonumber(u64[2], 16)}
    elseif tonumber(opnd) ~= nil then
      operand = {t = "CONST", n = tonumber(opnd)}
    elseif tonumber(opnd, 16) ~= nil then
      operand = {t = "CONST", n = tonumber(opnd,16)}
    else
      operand = {t = "NUM_UNDEF", n = opnd}
    end
  end
  -- set concrete const type
  if operand.t == "CONST" then
    if operand.n <= 0xf then
      operand.t = "NUM_4"
    elseif operand.n <= 0x1f then
      operand.t = "NUM_5"
    elseif operand.n <= 0xffff then
      operand.t = "NUM_16"
    elseif operand.n <= 0xffffffff then
      operand.t = "NUM_32"
    else
      werror("operand: "..tohex(operand.n).." is unsupported size")
    end
  end
  return operand
end

local function gen_code_dst(opnd)
  local value = 0
  local dst = check_operand(opnd)
  if dst.t == "BREG" then
    -- 0, reg_num(7)
    value = 0x0
    value = shl(value,7) + dst.n
  elseif dst.t == "RREG" then
    -- 1, 0, reg_num(6)
    value = 0x2
    value = shl(value,6) + dst.n
  elseif dst.t == "CTPR" then
    -- 1, 1, 0, 1, reg_num(4)
    value = 0xd
    value = shl(value,4) + dst.n
  elseif dst.t == "GREG" then
    -- 1, 1, 1, reg_num(5)
    value = 0x7
    value = shl(value,5) + dst.n
  else
    werror("operand of type: "..dst.t.." unsupported for dst")
  end
  return value
end

local function gen_code_src3(opnd)
  local value = 0
  local src3 = check_operand(opnd)
  if src3.t == "BREG" then
    -- 0, reg_num(7)
    value = 0x0
    value = shl(value,7) + src3.n
  elseif src3.t == "RREG" then
    -- 1, 0, reg_num(6)
    value = 0x2
    value = shl(value,6) + src3.n
  elseif src3.t == "GREG" then
    -- 1, 1, 1, reg_num(5)
    value = 0x7
    value = shl(value,5) + src3.n
  else
    werror("operand of type: "..src3.t.." unsupported for src3")
  end
  return value
end

local function add_literal(channel, src2)
  if wide_instr["LITERALS"] == nil then
    wide_instr["LITERALS"] = {}
  end

  local literals = wide_instr["LITERALS"]
  if src2.t == "NUM_16" or src2.t == "NUM_32" then
    for i,j in ipairs(literals) do
      if j.t == src2.t and j.n == src2.n then
        j.channels[#j.channels+1] = channel
        return
      end
    end
  elseif src2.t == "NUM_64" then
    for i,j in ipairs(literals) do
      if j.t == src2.t and j.lo == src2.lo and j.hi == src2.hi then
        j.channels[#j.channels+1] = channel
        return
      end
    end
  end

  if src2.t == "NUM_64" then
    literals[#literals+1] = {
      t = src2.t,
      lo = src2.lo,
      hi = src2.hi,
      channels = { channel },
    }
  else
    literals[#literals+1] = {
      t = src2.t,
      n = src2.n,
      channels = { channel },
    }
  end
end

local function gen_code_src2(opnd, channel)
  local value = 0
  local src2 = check_operand(opnd)
  if src2.t == "BREG" then
    -- 0, reg_num(7)
    value = 0x0
    value = shl(value,7) + src2.n
  elseif src2.t == "RREG" then
    -- 1, 0, reg_num(6)
    value = 0x2
    value = shl(value,6) + src2.n
  elseif src2.t == "GREG" then
    -- 1, 1, 1, reg_num(5)
    value = 0x7
    value = shl(value,5) + src2.n
  elseif src2.t == "NUM_4" then
    -- 1, 1, 0, 0, num_value(4)
    value = 0xc
    value = shl(value,4) + src2.n
  elseif ((src2.t == "NUM_5") or (src2.t == "NUM_16")) then
    src2.t = "NUM_16"
    add_literal(channel, src2)
  elseif src2.t == "NUM_32" then
    add_literal(channel, src2)
  elseif src2.t == "NUM_64" then
    add_literal(channel, src2)
  elseif src2.t == "NUM_UNDEF" then
    add_literal(channel, src2)
  else
    werror("Operand of type: "..src2.t.." unsupported for src2")
  end
  return value
end

local function gen_code_src1(opnd)
  local value = 0
  local src1 = check_operand(opnd)
  if src1.t == "BREG" then
    -- 0, reg_num(7), 0
    value = 0x0
    value = shl(value,7) + src1.n
  elseif src1.t == "RREG" then
    -- 1, 0, reg_num(6)
    value = 0x2
    value = shl(value,6) + src1.n
  elseif src1.t == "GREG" then
    -- 1, 1, 1, reg_num(5)
    value = 0x7
    value = shl(value,5) + src1.n
  elseif (src1.t == "NUM_4") or (src1.t == "NUM_5") then
    -- 1, 1, 0, num_value(5)
    value = 0x6
    value = shl(value,5) + src1.n
  else
    werror("operand of type: "..src1.t.." unsupported for src1")
  end
  return value
end

local function gen_code_pred(opnd)
  local value = 0
  local pred = check_operand(opnd)
  if ((pred.t ~= "PRED") and (pred.t ~= "IPRED")) then werror("Incorrect predicate register") end
  return pred.n
end

local function generate_setbn_oper(opc, rsz_seq, rbs_seq, rcur_seq)
  local code = 0
  local param_code = 0
  local rbs = assert(tonumber(sub(rbs_seq, 7)), "Incorrect rbs set")
  local rsz = assert(tonumber(sub(rsz_seq, 7)), "Incorrect rsz set")
  local rcur = assert(tonumber(sub(rcur_seq, 8)), "Incorrect rcur set")
  if (rbs == nil) or (rsz == nil) or (rcur == nil) then werror("Incorrect frame info") end
  if (rbs > 63) or (rsz > 63) or (rcur > 63) then werror("Incorrect frame info") end
  -- 32Bit opc(4), setbp(1), setbn(1), unused(3), psz(5), rcur(6), rsz(6), rbs(6)
  if wide_instr["CS1"] ~= nil then
    opc = band(sar(wide_instr["CS1"].value,28), 0xf)
    if (opc ~= 0x0) and (opc ~= 0x1) and (opc ~= 0x4) then
      werror("CS1 already busy")
    end
    param_code = shl(param_code,28) + band(wide_instr["CS1"].value, 0x0fffffff)
  end
  code = opc
  code = shl(code,2) + 0x1
  code = shl(code,8) + 0x0
  code = shl(code,6) + rcur
  code = shl(code,6) + rsz
  code = shl(code,6) + rbs
  code = bor(code, param_code)
  wide_instr["CS1"] = { value=code }
end

local function generate_setwd_oper(opc, wsz_seq, nfx_seq, dbl_seq)
  local code = 0
  local cs_code = 0
  local wsz = assert(tonumber(sub(wsz_seq, 7)), "Incorrect wsz set")
  local nfx = assert(tonumber(sub(nfx_seq, 7)), "Incorrect nfx set")
  local dbl = assert(tonumber(sub(dbl_seq, 7)), "Incorrect dbl set")
  if (wsz == nil) or (nfx == nil) or (dbl == nil) then werror("Incorrect frame info") end
  if (wsz > 127) or (nfx > 1) or (dbl > 1) then werror("Incorrect frame info") end
  -- 32Bit unused_hi(15), rpsz(5), wsz(7), nfx(1), dbl(1), unused_lo(3)
  code = shl(code,7) + wsz
  code = shl(code,1) + nfx
  code = shl(code,1) + dbl
  code = shl(code,3) + 0x0
  if wide_instr["CS1"] ~= nil then
    -- 32Bit opc(4), param(28)
    local cur_opc = band(sar(wide_instr["CS1"].value,28), 0xf)
    if (cur_opc ~= 0x0) and (cur_opc ~= 0x1) and (cur_opc ~= 0x4) then
      werror("CS1 already busy")
    end
    if cur_opc == 0x1 then opc = cur_opc end
    cs_code = opc
    cs_code = shl(cs_code,28) + band(wide_instr["CS1"].value, 0x0fffffff)
  else
    cs_code = opc
    cs_code = shl(cs_code,28) + 0x0
  end
  if wide_instr["LTS0"] ~= nil then
    if opc ~= 0x1 then werror("LTS0 already busy") end
  end
  wide_instr["LTS0"] = { value=code }
  wide_instr["CS1"] = { value=cs_code }
end

local function generate_ct_oper(opnd1, opnd2)
  local code = 0
  local ctpr = check_operand(opnd1)
  -- 32Bit, ipd(2),eap(1),bap(1),rp_hi(1),vfdi(1),rp_lo(1),abg(2),abn(2),type(1),
  --        abp(2),alc(2),aa(4),ctop(2),unused(1),ctcond(9)
  code = 0x3
  code = shl(code,20) + ctpr.n
  code = shl(code,10)
  if opnd2 ~= nil then
    -- ct(4), pred_num(5)
    local value = 0
    local pred = check_operand(opnd2)
    if pred.t == "IPRED" then
      value = 0x3
    elseif pred.t == "PRED" then
      value = 0x2
    else
      werror("Operand of type: "..pred.t.." unsupported for condition")
    end
    value = shl(value,5) + pred.n
    code = code + value
  else
    -- set always
    code = code + 0x20
  end
  if wide_instr["SS"] ~= nil then
    if band(sar(wide_instr["SS"].value, 30), 0x3) == 0x3 then
      werror("device is already busy")
    end
    wide_instr["SS"].value = bor(wide_instr["SS"].value, code)
  else
    wide_instr["SS"] = { value=code }
  end
end

local function generate_call_oper(opc, opnd1, opnd2)
  local code = 0
  if wide_instr["CS1"] ~= nil then werror("CS1 already busy") end
  generate_ct_oper(opnd1)
  local wbs = tonumber(sub(opnd2, 7))
  if wbs == nil then werror("incorrect wbs value") end
  -- 32Bit opc(4), unused(21), wbs(7)
  code = opc
  code = shl(code,21) + 0x0
  code = shl(code,7) + wbs
  wide_instr["CS1"] = { value=code }
end

local function generate_disp_oper(oper, opc, opnd1, opnd2)
  local code = 0
  local ctpr = check_operand(opnd1)
  assert(ctpr.t == "CTPR", "Incorrect register for dist")
  assert(wide_instr["CS0"] == nil, "CS0 already busy")
  -- 32Bit, ctpr(2), opcode(2), disp_value(28)
  code = ctpr.n
  code = shl(code,2) + opc
  code = shl(code,28) + 0x0
  if oper == "RETURN" then
    assert(ctpr.n == 3, "Incorrect register for return, should be ctpr3")
    wide_instr["CS0"] = { value=code }
  elseif oper == "DISP" then
    local label = check_operand(opnd2)
    assert(label.t == "NUM_UNDEF", "Incorrect label set")
    wide_instr["CS0"] = { value=code, action="LABEL", lit=label.n }
  else
    werror("Unsupported disp operation")
  end
end

local function gen_code_alf1(channel, spec, cop, src1, src2, dst)
  local code = 0
  -- 32bit, spec(1), cop(7), src1(8), src2(8), dst(8)
  code = spec
  code = shl(code,7) + cop
  code = shl(code,8) + gen_code_src1(src1)
  code = shl(code,8) + gen_code_src2(src2, channel)
  code = shl(code,8) + gen_code_dst(dst)
  wide_instr["ALS"..channel] = { value=code }
end

local function gen_code_alf2(channel, spec, cop, opce, src2, dst)
  local code = 0
  -- 32bit, spec(1), cop(7), opce(8), src2(8), dst(8)
  code = spec
  code = shl(code,7) + cop
  code = shl(code,8) + opce
  code = shl(code,8) + gen_code_src2(src2, channel)
  code = shl(code,8) + gen_code_dst(dst)
  wide_instr["ALS"..channel] = { value=code }
end

local function gen_code_alf3(channel, spec, cop, src1, src2, src3)
  local code = 0
  -- 32bit, spec(1), cop(7), src1(8), src2(8), src3(8)
  code = spec
  code = shl(code,7) + cop
  code = shl(code,8) + gen_code_src1(src1)
  code = shl(code,8) + gen_code_src2(src2, channel)
  code = shl(code,8) + gen_code_src3(src3)
  wide_instr["ALS"..channel] = { value=code }
end

local function gen_code_alf7(channel, spec, cop, opce, src1, src2, pred)
    -- 32Bit, spec(1), cop(7), src1(8), src2(8), cmpopce(3), pdst(5)
    code = spec
    code = shl(code,7) + cop
    code = shl(code,8) + gen_code_src1(src1)
    code = shl(code,8) + gen_code_src2(src2, channel)
    code = shl(code,3) + opce
    code = shl(code,5) + gen_code_pred(pred)
    wide_instr["ALS"..channel] = { value=code }
end

local function gen_code_alef1(channel, ales_opc2, src3)
  local code = 0
  -- 16bit, opc2(8), src3(8)
  code = ales_opc2
  code = shl(code,8) + gen_code_src3(src3)
  wide_instr["ALES"..channel] = { value=code }
end

local function gen_code_alef2(channel, ales_opc2, ales_opce)
  local code = 0
  -- 16bit, opc2(8), opce(8)
  code = ales_opc2
  code = shl(code,8) + ales_opce
  wide_instr["ALES"..channel] = { value=code }
end

local function generate_alu_oper(format, spec, channel, op_channel, cop, opce, ales_opc2, ales_opce, opnd1, opnd2, opnd3, opnd4)
  local code = 0
  assert(channel >=0 and channel <= 5, "Incorrect channel should be 1-5")
  if band(2 ^ channel, op_channel) == 0 then werror("Incorrect channel for this operation") end
  if wide_instr["ALS"..channel] ~= nil then werror("ALS"..channel.." already busy") end
  if format == "ALOPF1" then
    gen_code_alf1(channel, spec, cop, opnd1, opnd2, opnd3)
  elseif format == "ALOPF11" then
    gen_code_alf1(channel, spec, cop, opnd1, opnd2, opnd3)
    gen_code_alef2(channel, ales_opc2, ales_opce)
  elseif format == "ALOPF12" then
    gen_code_alf2(channel, spec, cop, opce, opnd1, opnd2)
    gen_code_alef2(channel, ales_opc2, ales_opce)
  elseif format == "ALOPF2" then
    gen_code_alf2(channel, spec, cop, opce, opnd1, opnd2)
  elseif format == "ALOPF3" then
    gen_code_alf3(channel, spec, cop, opnd1, opnd2, opnd3)
  elseif format == "ALOPF7" then
    gen_code_alf7(channel, spec, cop, opce, opnd1, opnd2, opnd3)
  elseif format == "ALOPF21" then
    gen_code_alf1(channel, spec, cop, opnd1, opnd2, opnd4)
    gen_code_alef1(channel, ales_opc2, opnd3)
  else
    werror("Unsupported format")
  end
end

local function generate_alu_cond(channel, opnd)
  local opc = 0
  local psrc = 0
  local code = 0
  local pred = check_operand(opnd)
  if band(2 ^ channel, 0x7) == 0 then opc = 1 end
  if pred.t == "PRED" or pred.t == "IPRED" then
    -- 7bit, 1, 1, psrc
    psrc = 3
    psrc = shl(psrc, 5) + pred.n
  else
    werror("Unsupported predicate type")
  end
  local found = false
  for i,j in ipairs({"CDS00", "CDS01", "CDS10", "CDS11", "CDS20", "CDS21"}) do
    if wide_instr[j] == nil then
      local mask = 0
      local neg = 0
      if band(2 ^ channel, 0x9) ~= 0 then mask = 1
      elseif band(2 ^ channel, 0x12) ~= 0 then mask = 2
      elseif band(2 ^ channel, 0x24) ~= 0 then mask = 4 end
      if pred.t == "IPRED" then
        if band(2 ^ channel, 0x9) ~= 0 then neg = 1
        elseif band(2 ^ channel, 0x12) ~= 0 then neg = 2
        elseif band(2 ^ channel, 0x24) ~= 0 then neg = 4 end
      end
      -- 16bit, opc(2), mask(4), neg(3), pred(7)
      code = opc
      code = shl(code, 4) + mask
      code = shl(code, 3) + neg
      code = shl(code, 7) + psrc
      wide_instr[j] = { value=code }
      found = true
      break
    end
  end
  if found == false then werror("No empty CDS for conditional alu operation") end
end

local function generate_landp_oper(opc, opnd1, opnd2, opnd3)
  local pred1 = check_operand(opnd1)
  local pred2 = check_operand(opnd2)
  local res = check_operand(opnd3)
  local pls = nil
  local code = 0
  if (pred1.t ~= "LPRED" and pred1.t ~= "LIPRED")
         or (pred2.t ~= "LPRED" and pred2.t ~= "LIPRED")
         or res.t ~= "LPRED" then werror("Incorrect predicate") end
  if res.n == 4 then pls = 0
  elseif res.n == 5 then pls = 1
  elseif res.n == 6 then pls = 2
  else werror("Incorrect local predicate") end
  if wide_instr["PLS"..pls] ~= nil then
    code = wide_instr["PLS"..pls].value
    if band(code, 0xffff) ~= 0 then werror("PLS already busy") end
  end
  -- clp 16bit, opc(2), neg0(1), p0(3), neg1(1), p1(3), vdst(1), pdst(5)
  local clp_code = 0
  clp_code = opc
  clp_code = shl(clp_code, 1)
  if pred1.t == "LIPRED" then
    clp_code = clp_code + 1
  end
  clp_code = shl(clp_code, 3) + pred1.n
  clp_code = shl(clp_code, 1)
  if pred2.t == "LIPRED" then
    clp_code = clp_code + 1
  end
  clp_code = shl(clp_code,3) + pred2.n
  clp_code = shl(clp_code,6)
  wide_instr["PLS"..pls] = { value=bor(code, clp_code) }
end

local function generate_pass_oper(opnd1, opnd2)
  local pred1 = check_operand(opnd1)
  local pred2 = check_operand(opnd2)
  local pls = nil
  local code = 0
  if pred1.t == "PRED" then
    if pred2.t ~= "LPRED" then werror("Incorrect local predicate") end
    if pred2.n == 0 or pred2.n == 1 then pls = 0
    elseif pred2.n == 2 or pred2.n == 3 then pls = 1
    else werror("Incorrect local predicate") end
    if wide_instr["PLS"..pls] ~= nil then
      code = wide_instr["PLS"..pls].value
    end
    -- elp 7bit, 1, 1, psrc(5)
    local elp_code = 3
    elp_code = shl(elp_code, 5) + pred1.n
    -- 32bit, unused(1), elp(7), unused(1), elp(7), clp(16)
    if pred2.n == 0 or pred2.n == 2 then
      if band(code, 0x7f000000) == 0 then
        elp_code = shl(elp_code, 24)
      else
        werror("PLS already busy")
      end
    elseif pred2.n == 1 or pred2.n == 3 then
      if band(code, 0x7f0000) == 0 then
        elp_code = shl(elp_code, 16)
      else
        werror("PLS already busy")
      end
    end
    wide_instr["PLS"..pls] = { value=bor(code, elp_code) }
  elseif pred1.t == "LPRED" then
    if pred2.t ~= "PRED" then werror("Incorrect predicate") end
    if pred1.n == 4 then pls = 0
    elseif pred1.n == 5 then pls = 1
    elseif pred1.n == 6 then pls = 2
    else werror("Incorrect local predicate") end
    if wide_instr["PLS"..pls] ~= nil then
      code = wide_instr["PLS"..pls].value
    end
    -- clp 16bit, opc(2), neg0(1), p0(3), neg1(1), p1(3), vdst(1), pdst(5)
    local clp_code = 1
    clp_code = shl(clp_code, 5) + pred2.n
    -- 32bit, unused(1), elp(7), unused(1), elp(7), clp(16)
    wide_instr["PLS"..pls] = { value=bor(code, clp_code) }
  else
    werror("Incorrect operands for pass")
  end
end

local function generate_nop_oper(opnd)
  local val = tonumber(opnd)
  if val == nil then werror("Incorrect nop value") end
  if val == 0 then wwarn("Ignoring nop 0") end
  if wide_instr["NOP"] == nil then
    wide_instr["NOP"] = { value=val }
  else
    werror("Nop already set")
  end
end

local function update_src2(channels, value)
  for i,channel in ipairs(channels) do
    local als = wide_instr["ALS"..channel]
    als.value = bor(als.value, shl(value, 8))
  end
end

local function generate_lts16()
  for i,lit in ipairs(wide_instr["LITERALS"]) do
    if lit.t == "NUM_16" then
      local found = false
      for i,j in ipairs({ "LTS0", "LTS1" }) do
        if wide_instr[j] == nil then
          wide_instr[j] = { value=lit.n, half = true }
          -- 1, 1, 0, 1, 0, lts_hi, lts_num
          update_src2(lit.channels, 0xd0 + i - 1)
          found = true
          break
        elseif wide_instr[j].half == true then
          wide_instr[j].half = nil
          wide_instr[j].value = bor(wide_instr[j].value, shl(lit.n, 16))
          -- 1, 1, 0, 1, 0, lts_lo, lts_num
          update_src2(lit.channels, 0xd4 + i - 1)
          found = true
          break
        end
      end
      if not found then
        -- Try 32-bit.
        lit.t = "NUM_32"
      end
    end
  end
end

local function generate_lts32()
  for i,lit in ipairs(wide_instr["LITERALS"]) do
    if lit.t == "NUM_32" then
      local found = false
      for i,j in ipairs({ "LTS0", "LTS1", "LTS2", "LTS3" }) do
        if wide_instr[j] == nil then
          wide_instr[j] = { value=lit.n }
          -- 1, 1, 0, 1, 1, 0, lts_num
          local value = 0xd8 + i - 1
          update_src2(lit.channels, value)
          found = true
          break
        end
      end
      if not found then
        return false
      end
    elseif lit.t == "NUM_UNDEF" then
      -- set it to undef_lit32, hope, all of them not bigger that
      local name, tail = match(lit.n, "^([%w_]+)(->.*)$")
      -- also check for arrays
      if tail == nil then
        name, tail = match(lit.n, "^([%w_]+)(%[[%d]+%])$")
      end
      if tail ~= nil then
        name = format(map_type[name].ctypefmt, tail)
      else
        name = lit.n
      end
      local found = false
      for i,j in ipairs({ "LTS0", "LTS1", "LTS2", "LTS3" }) do
        if wide_instr[j] == nil then
          wide_instr[j] = { value=0x0, action="IMM", lit=name }
          -- 1, 1, 0, 1, 1, 0, lit_num
          value = 0x36
          value = shl(value,2) + i - 1
          update_src2(lit.channels, value)
          found = true
          break
        end
      end
      if not found then
        return false
      end
    end
  end
  return true
end

local function generate_lts64()
  for i,lit in ipairs(wide_instr["LITERALS"]) do
    if lit.t == "NUM_64" then
      local found = false
      for i,j in ipairs({ "LTS0", "LTS1", "LTS2" }) do
        if (wide_instr["LTS"..i] == nil) and (wide_instr[j] == nil) then
          wide_instr[j] = { value = lit.lo }
          wide_instr["LTS"..i] = { value = lit.hi }
          -- 1, 1, 0, 1, 1, 1, lit_num
          local value = 0x37
          value = shl(value,2) + i - 1
          update_src2(lit.channels, value)
          found = true
          break
        end
      end
      if not found then
        return false
      end
    end
  end
  return true
end

local function generate_lts()
  if wide_instr["LITERALS"] ~= nil then
    generate_lts16()
    if not generate_lts32() or not generate_lts64() then
      wide_instr["LITERALS"] = nil
      werror("Not enough space for literals")
    end
  end
end

local function generate_hs_code()
  -- look for syls, in f1 one of them HS himself
  local num_sylf1 = 1
  for _,i in ipairs({ "SS", "ALS0", "ALS1", "ALS2", "ALS3", "ALS4", "ALS5", "CS0" }) do
    if wide_instr[i] ~= nil then
      num_sylf1 = num_sylf1 + 1
    end
  end
  -- skip ALES2, ALES5, they are >=elbrus-v4 only
  local num_sylf2 = 0
  if wide_instr["CS1"] then num_sylf2 = num_sylf2 + 1 end
  local num_sylf3 = 0
  for _,i in ipairs({ "ALES0", "ALES1", "ALES3", "ALES4", "AAS0", "AAS1", "AAS2", "AAS3", "AAS4", "AAS5" }) do
    if wide_instr[i] ~= nil then
      num_sylf3 = num_sylf3 + 1
    end
  end
  -- half syls
  num_sylf3 = sar(num_sylf3, 1) + (num_sylf3 % 2)
  local num_sylf4 = 0
  if wide_instr["LTS3"] ~= nil then
    num_sylf4 = num_sylf4 + 4
  elseif wide_instr["LTS2"] ~= nil then
    num_sylf4 = num_sylf4 + 3
  elseif (wide_instr["LTS1"] ~= nil) or (wide_instr["LTS1_LO"] ~= nil) or (wide_instr["LTS1_HI"] ~= nil) then
    num_sylf4 = num_sylf4 + 2
  elseif (wide_instr["LTS0"] ~= nil) or (wide_instr["LTS0_LO"] ~= nil) or (wide_instr["LTS0_HI"] ~= nil) then
    num_sylf4 = num_sylf4 + 1
  end
  local hs_pls = 0
  if wide_instr["PLS2"] ~= nil then
    num_sylf4 = num_sylf4 + 3
    hs_pls = 3
  elseif wide_instr["PLS1"] ~= nil then
    num_sylf4 = num_sylf4 + 2
    hs_pls = 2
  elseif wide_instr["PLS0"] ~= nil then
    num_sylf4 = num_sylf4 + 1
    hs_pls = 1
  end
  local hs_cds = 0
  if (wide_instr["CDS20"] ~= nil) or (wide_instr["CDS21"] ~= nil) then
    num_sylf4 = num_sylf4 + 3
    hs_cds = 3
  elseif (wide_instr["CDS10"] ~= nil) or (wide_instr["CDS11"] ~= nil) then
    num_sylf4 = num_sylf4 + 2
    hs_cds = 2
  elseif (wide_instr["CDS00"] ~= nil) or (wide_instr["CDS01"] ~= nil) then
    num_sylf4 = num_sylf4 + 1
    hs_cds = 1
  end
  local hs_als = 0
  if wide_instr["ALS5"] ~= nil then hs_als = 0x20 end
  if wide_instr["ALS4"] ~= nil then hs_als = hs_als + 0x10 end
  if wide_instr["ALS3"] ~= nil then hs_als = hs_als + 0x8 end
  if wide_instr["ALS2"] ~= nil then hs_als = hs_als + 0x4 end
  if wide_instr["ALS1"] ~= nil then hs_als = hs_als + 0x2 end
  if wide_instr["ALS0"] ~= nil then hs_als = hs_als + 0x1 end
  local code = hs_als -- set al
  local hs_ales = 0
  if wide_instr["ALES5"] ~= nil then hs_ales = 0x20 end
  if wide_instr["ALES4"] ~= nil then hs_ales = hs_ales + 0x10 end
  if wide_instr["ALES3"] ~= nil then hs_ales = hs_ales + 0x8 end
  if wide_instr["ALES2"] ~= nil then hs_ales = hs_ales + 0x4 end
  if wide_instr["ALES1"] ~= nil then hs_ales = hs_ales + 0x2 end
  if wide_instr["ALES0"] ~= nil then hs_ales = hs_ales + 0x1 end
  code = shl(code,6) + hs_ales -- set ale
  code = shl(code,2) + hs_pls -- set pl
  code = shl(code,2) + hs_cds -- set cd
  local hs_c = 0
  if wide_instr["CS1"] ~= nil then hs_c = 2 end
  if wide_instr["CS0"] ~= nil then hs_c = hs_c + 1 end
  code = shl(code,2) + hs_c -- set c
  if wide_instr["SS"] ~= nil then
    code = shl(code,2) + 1 -- set s + sw
  else
    code = shl(code,2) + 0
  end
  code = shl(code,1) + 0 -- set x
  code = shl(code,1) + 0 -- set lm (will not support loop mode in first steps)
  if wide_instr["NOP"] ~= nil then
    code = shl(code,3) + wide_instr["NOP"].value -- set nop
  else
    code = shl(code,3) + 0
  end
  local hs_lng = num_sylf1 + num_sylf2 + num_sylf3 + num_sylf4
  local is_notaligned = false
  if (hs_lng % 2) ~= 0 then
    hs_lng = hs_lng + 1
    is_notaligned = true
  end
  code = shl(code,3) + (sar(hs_lng, 1) - 1) -- set lng
  code = shl(code,4) + num_sylf1 + num_sylf2 -1 -- set mdl
  return code, is_notaligned
end

local function generate_ins_code(hs_code, is_notaligned)
  local ins = {}
  ins[#ins+1] = { value = hs_code }
  local syls = { "SS", "ALS0", "ALS1", "ALS2", "ALS3", "ALS4", "ALS5", "CS0", "CS1" }
  for i,j in ipairs(syls) do
    if wide_instr[j] ~= nil then ins[#ins+1] = wide_instr[j] end
  end
  local half_syls = { "ALES0", "ALES1", "ALES3", "ALES4", "AAS0", "AAS1", "AAS2", "AAS3", "AAS4", "AAS5" }
  local tmp_code = 0
  for i,j in ipairs(half_syls) do
    if wide_instr[j] ~= nil then
      if tmp_code ~= 0 then
        ins[#ins+1] = { value = shl(tmp_code, 16) + wide_instr[j].value}
        tmp_code = 0
      else
        tmp_code = wide_instr[j].value
      end
    end
  end
  if tmp_code ~= 0 then ins[#ins+1] = { value = shl(tmp_code, 16) } end
  if is_notaligned then ins[#ins+1] = { value = 0x0 } end
  syls = { "LTS3", "LTS2", "LTS1", "LTS0", "PLS2", "PLS1", "PLS0" }
  for i,j in ipairs(syls) do
    if wide_instr[j] ~= nil then ins[#ins+1] = wide_instr[j] end
  end
  for i,j in ipairs({ "CDS2", "CDS1", "CDS0"}) do
    tmp_code = 0
    if wide_instr[j.."0"] ~= nil then
      tmp_code = shl(wide_instr[j.."0"].value, 16)
    end
    if wide_instr[j.."1"] ~= nil then
      tmp_code = bor(wide_instr[j.."1"].value, tmp_code)
    end
    if tmp_code ~= 0 then
      ins[#ins+1] = { value = tmp_code }
    end
  end
  return ins
end

local function wide_gen(force)
  if not force and not wide_capture then
    return
  end
  -- Stop capturing bundle instructions.
  wide_capture = false
  generate_lts()
  local hs_code, is_notaligned = generate_hs_code()
  local code = generate_ins_code(hs_code, is_notaligned)
  local actions = {}
  for i,j in ipairs(code) do
    wputxw(j.value)
    if j.action then
      if j.action == "LABEL" then
        local mode, n, s = parse_label(j.lit, false)
        local ofs_e = #code - i + 1
        local ofs_s = #code / 2
        assert(ofs_e < 15, "Too big offset to CS0")
        assert(ofs_s < 15, "Too big size of command")
        actions[#actions+1] = { "REL_"..mode, n, s, ofs_e, ofs_s, 1 }
      elseif j.action == "IMM" then
        local ofs = #code - i + 1
        actions[#actions+1] = { "IMM", 0, j.lit, ofs, nil, 1 }
      else
        werror("Incompatible action")
      end
    end
  end
  for i,j in ipairs(actions) do
    waction(j[1], j[2], j[3], j[4], j[5], j[6])
  end
  for i in pairs(wide_instr) do
    wide_instr[i] = nil
  end
end

map_op[".template__"] = function(params, template)
  if not params then return template end
  -- Get operation info and format
  local op_info = {}
  for t in gmatch(template, "[^_]+") do
    op_info[#op_info+1] = t
  end

  -- Check type of command
  local op_type = op_info[1]
  if sub(op_type, 1, 3) == "ALU" then
    local format = op_info[2]
    local spec = assert(tonumber(op_info[3]), "Incorrect speculating set")
    local channel = assert(tonumber(params[1]), "Incorrect channel set")
    local op_channel = assert(tonumber(op_info[4]), "Incorrect supported channel mask")
    local cop = assert(tonumber(op_info[5]), "Incorrect cop set")
    if op_type == "ALU1" or op_type == "ALU1PR" then
      local opce = op_info[6] -- May be nil, check later.
      local ales_opc2 = op_info[7] -- May be nil, check later.
      local ales_opce = op_info[8] -- May be nil, check later.
      generate_alu_oper(format, spec, channel, op_channel,
                            cop, opce, ales_opc2, ales_opce,
                            params[2], params[3])
      if op_type == "ALU1PR" then generate_alu_cond(channel, params[4]) end
    elseif op_type == "ALU2" or op_type == "ALU2PR" then
      local opce = op_info[6] -- May be nil, check later.
      local ales_opc2 = op_info[7] -- May be nil, check later.
      local ales_opce = op_info[8] -- May be nil, check later.
      generate_alu_oper(format, spec, channel, op_channel,
                            cop, opce, ales_opc2, ales_opce,
                            params[2], params[3], params[4])
      if op_type == "ALU2PR" then generate_alu_cond(channel, params[5]) end
    elseif op_type == "ALU3" then
      local opce = op_info[6] -- May be nil, check later.
      local ales_opc2 = op_info[7] -- May be nil, check later.
      local ales_opce = op_info[8] -- May be nil, check later.
      generate_alu_oper(format, spec, channel, op_channel, 
                            cop, opce, ales_opc2, ales_opce,
                            params[2], params[3], params[4], params[5])
    else
      werror("Unsupported ALU operation")
    end
  elseif op_type == "DISP" then
    local operation = op_info[2]
    local opc = assert(tonumber(op_info[3]), "Incorrect opcode set")
    generate_disp_oper(operation, opc, params[1], params[2])
  elseif op_type == "CT" then
    generate_ct_oper(params[1], params[2])
  elseif op_type == "CALL" then
    local opc = assert(tonumber(op_info[2]), "Incorrect opcode set")
    generate_call_oper(opc, params[1], params[2])
  elseif op_type == "SETWD" then
    local opc = assert(tonumber(op_info[2]), "Incorrect opcode set")
    generate_setwd_oper(opc, params[1], params[2], params[3])
  elseif op_type == "SETBN" then
    local opc = assert(tonumber(op_info[2]), "Incorrect opcode set")
    generate_setbn_oper(opc, params[1], params[2], params[3])
  elseif op_type == "PASS" then
    generate_pass_oper(params[1], params[2])
  elseif op_type == "LANDP" then
    local opc = assert(tonumber(op_info[2]), "Incorrect opcode set")
    generate_landp_oper(opc, params[1], params[2], params[3])
  elseif op_type == "NOP" then
    generate_nop_oper(params[1])
  elseif op_type == "GEN" then
    -- User requested to generate a bundle.
    wide_gen(true)
    if not wide_mode then
      wide_mode = true
      werror("Bundle end `--` cannot be used if wide mode is disabled")
    end
    return
  else
    werror("Incorrect operation type")
  end

  if wide_mode then
    -- Start capturing instructions.
    wide_capture = true
  else
    wide_gen(true)
  end
end

------------------------------------------------------------------------------

-- Pseudo-opcodes to switch wide mode
map_op[".wide_1"] = function(params)
  if params[1] == "on" or params[1] == "off" then
    wide_mode = params[1] == "on"
    if not wide_mode then
      wide_gen(false)
    end
  else
    werror("Expected \"on\" or \"off\"")
  end
end

------------------------------------------------------------------------------

-- Pseudo-opcode to mark the position where the action list is to be emitted.
map_op[".actionlist_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeactions(out, name) end)
end

-- Pseudo-opcode to mark the position where the global enum is to be emitted.
map_op[".globals_1"] = function(params)
  if not params then return "prefix" end
  local prefix = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeglobals(out, prefix) end)
end

-- Pseudo-opcode to mark the position where the global names are to be emitted.
map_op[".globalnames_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeglobalnames(out, name) end)
end

-- Pseudo-opcode to mark the position where the extern names are to be emitted.
map_op[".externnames_1"] = function(params)
  if not params then return "cvar" end
  local name = params[1] -- No syntax check. You get to keep the pieces.
  wline(function(out) writeexternnames(out, name) end)
end

------------------------------------------------------------------------------

-- Label pseudo-opcode (converted from trailing colon form).
map_op[".label_1"] = function(params)
  -- Always generate bundle before a label.
  wide_gen(false)
  if not params then return "[1-9] | ->global | =>pcexpr" end
  if secpos+1 > maxsecpos then wflush() end
  local mode, n, s = parse_label(params[1], true)
  if mode == "EXT" then werror("bad label definition") end
  waction("LABEL_"..mode, n, s, nil, nil, 1)
end

------------------------------------------------------------------------------

-- Pseudo-opcode for (primitive) type definitions (map to C types).
map_op[".type_3" ] = function(params, nparams)
  if not params then
    return nparams == 2 and "name, ctype" or "name, ctype, reg"
  end
  local name, ctype = params[1], params[2], params[3]
  if not match(name, "^[%a_][%w_]*$") then
    werror("bad type name `"..name.."'")
  end
  local tp = map_type[name]
  if tp then
    werror("duplicate type `"..name.."'")
  end
  -- Add #type to defines. A bit unclean to put it in map_archdef.
  map_archdef["#"..name] = "sizeof("..ctype..")"
  -- Add new type and emit shortcut define.
  local num = ctypenum + 1
  map_type[name] = {
    ctype = ctype,
    ctypefmt = format("Dt%X(%%s)", num),
    reg = reg,
  }
  wline(format("#define Dt%X(_V) (int)(ptrdiff_t)&(((%s *)0)_V)", num, ctype))
  ctypenum = num
end
map_op[".type_2"] = map_op[".type_3"]

-- Dump type definitions.
local function dumptypes(out, lvl)
  local t = {}
  for name in pairs(map_type) do t[#t+1] = name end
  sort(t)
  out:write("Type definitions:\n")
  for _,name in ipairs(t) do
    local tp = map_type[name]
    local reg = tp.reg or ""
    out:write(format("  %-20s %-20s %s\n", name, tp.ctype, reg))
  end
  out:write("\n")
end

------------------------------------------------------------------------------

-- Set the current section.
function _M.section(num)
  -- Always generate bundle before a label.
  wide_gen(false)
  waction("SECTION", num)
  wflush(true) -- SECTION is a terminal action.
end

------------------------------------------------------------------------------

-- Dump architecture description.
function _M.dumparch(out)
  out:write(format("DynASM %s version %s, released %s\n\n",
    _info.arch, _info.version, _info.release))
  dumpactions(out)
end

-- Dump all user defined elements.
function _M.dumpdef(out, lvl)
  dumptypes(out, lvl)
  dumpglobals(out, lvl)
  dumpexterns(out, lvl)
end

------------------------------------------------------------------------------

-- Pass callbacks from/to the DynASM core.
function _M.passcb(wl, we, wf, ww)
  wline, werror, wfatal, wwarn = wl, we, wf, ww
  return wflush
end

-- Setup the arch-specific module.
function _M.setup(arch, opt)
  g_arch, g_opt = arch, opt
end

-- Merge the core maps and the arch-specific maps.
function _M.mergemaps(map_coreop, map_def)
  setmetatable(map_op, { __index = map_coreop })
  setmetatable(map_def, { __index = map_archdef })
  return map_op, map_def
end

return _M

------------------------------------------------------------------------------

