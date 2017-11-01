{-# LANGUAGE CPP #-}

#include "HsVersions.h"
#include "nativeGen/NCG.h"

module ARM.Instr (
  RI(..),
  Instr(..)
) where

import           GhcPrelude

import           Format
import           Instruction
import           PPC.Cond
import           PPC.Regs
import           Reg
import           RegClass
import           TargetReg

import           BlockId
import           CLabel
import           Cmm
import           CmmInfo
import           CodeGen.Platform
import           DynFlags
import           FastString
import           Hoopl.Collections
import           Hoopl.Label
import           Outputable
import           Platform
import           UniqFM            (listToUFM, lookupUFM)
import           UniqSupply

import           Control.Monad     (replicateM)
import           Data.Maybe        (fromMaybe)

data Cond
  = EQ -- Equal
  | NE -- Not equal
  | CS -- Carry Set / Unsigned higher or same
  | CC -- Carry Set / Unsigned higher or same
  | MI -- Negative
  | PL -- Positive or zero
  | VS -- Overflow
  | VC -- Overflow
  | HI -- Unsigned higher
  | LS -- Unsigned lower or same
  | GE -- Signed greater than or equal
  | LT -- Signed less than
  | GT -- Signed greater than
  | LE -- Signed less than or equal
  | AL -- Always
  deriving Eq

data Size
  = B   -- byte
  | SB  -- byte (signed)
  | H   -- half word
  | SH  -- half-word (signed)
  deriving Eq

-- Register or immediate.
data RI     = RIReg Reg | RIImm Imm
type Offset = RI

data Op2
  = Op2     Reg
  | Op2'    Imm
  | Op2LSL  Reg Reg
  | Op2LSL' Reg Imm
  | Op2LSR  Reg Reg
  | Op2LSR' Reg Imm
  | Op2ASR  Reg Reg
  | Op2ASR' Reg Imm
  | Op2ROR  Reg Reg
  | Op2ROR' Reg Imm

type Rd       = Reg
type Rn       = Reg
type Rm       = Reg
type Rs       = Reg
type Fd       = Reg
type Fn       = Reg
type Fm       = Reg
type Constant = Word32

data Prec
  = F32
  | F64

data Instr
  -- Loads and stores.
  = LDR   Cond Rd Address
  | LDR'  Cond Rd Imm               -- Assembler creates MOV or LDR from lit pool
  | LDRB  Cond Rd Address
  | STR   Cond Rd Address
  | STRB  Cond Rd Address
  -- Arithmetic operations.
  | ADD   Cond Rd Rn Op2            -- Rd := Rn + Op2
  | ADC   Cond Rd Rn Op2            -- Rd := Rn + Op2 + Carry
  | SUB   Cond Rd Rn Op2            -- Rd := Rn – Op2
  | SBC   Cond Rd Rn Op2            -- Rd := Rn – Op2 – NOT(Carry)
  | MUL   Cond Rd Rm Rs             -- Rd := (Rm * Rs)[31:0]
  | SDIV  Cond Rd Rn Rm             -- Rd := Rn / Rm
  | UDIV  Cond Rd Rn Rm             -- Rd := Rn / Rm
  -- Moves operations.
  | MOV   Cond Rd    Op2            -- Rd := Op2
  | MOVS  Cond Rd    Op2            -- Rd := Op2
  | MVN   Cond Rd    Op2            -- Rd := 0xFFFFFFFF EOR Op2
  | MVNS  Cond Rd    Op2            -- Rd := 0xFFFFFFFF EOR Op2
  -- Compare operations.
  | CMP   Cond    Rn Op2            -- Update CPSR flags on Rn – Op2
  | CMN   Cond    Rn Op2            -- Update CPSR flags on Rn + Op2
  -- Logical operations.
  | TST   Cond    Rn Op2            -- Update CPSR flags on Rn AND Op2
  | TEQ   Cond    Rn Op2            -- Update CPSR flags on Rn EOR Op2
  | AND   Cond Rd Rn Op2            -- Rd := Rn AND Op2
  | EOR   Cond Rd Rn Op2            -- Rd := Rn EOR Op2
  | ORR   Cond Rd Rn Op2            -- Rd := Rn ORR Op2
  | ORN   Cond Rd Rn Op2            -- Rd := Rn ORN Op2
  | BIC   Cond Rd Rn Op2            -- Rd := Rn AND NOT Op2
  -- Swap instruction.
  | SWP   Cond Rd Rm Rn             -- temp := [Rn], [Rn] := Rm, Rd := temp
  | SWPB  Cond Rd Rm Rn             -- temp := ZeroExtend([Rn][7:0]), [Rn][7:0] := Rm[7:0], Rd := temp
  -- Software interrupt instruction.
  | SWI   Cond Imm
  -- Jump instructions.
  | B     Cond Label                -- R15 := label
  -- Floating point instructions.
  | VADD  Cond Prec Fd Fn Fm
  | VSUB  Cond Prec Fd Fn Fm
  | VDIV  Cond Prec Fd Fn Fm
  | VABS  Cond Prec Fd    Fm
  | VNEG  Cond Prec Fd    Fm
  | VSQRT Cond Prec Fd    Fm
  | VCMP  Cond Prec Fd    Fm

instance Instruction Instr where
  regUsageOfInstr         = arm_regUsageOfInstr
  patchRegsOfInstr        = arm_patchRegsOfInstr
  isJumpishInstr          = arm_isJumpishInstr
  jumpDestsOfInstr        = arm_jumpDestsOfInstr
  patchJumpInstr          = arm_patchJumpInstr
  mkSpillInstr            = arm_mkSpillInstr
  mkLoadInstr             = arm_mkLoadInstr
  takeDeltaInstr          = arm_takeDeltaInstr
  isMetaInstr             = arm_isMetaInstr
  mkRegRegMoveInstr _     = arm_mkRegRegMoveInstr
  takeRegRegMoveInstr     = arm_takeRegRegMoveInstr
  mkJumpInstr             = arm_mkJumpInstr
  mkStackAllocInstr       = arm_mkStackAllocInstr
  mkStackDeallocInstr     = arm_mkStackDeallocInstr

-- TODO: Does the cpsr register have to be considered here?
-- TODO: Implement usgAddr and usgOp2!
arm_reqUsageOfInstr :: Platform -> Instr -> RegUsage
arm_reqUsageOfInstr platform instr = case instr of
  -- Loads and stores.
  LDR  _ rd ad    -> dst [rd] +++ usgAddr ad
  LDRB _ rd ad    -> dst [rd] +++ usgAddr ad
  STR  _ rd ad    -> src [rd] +++ usgAddr ad
  STRB _ rd ad    -> src [rd] +++ usgAddr ad
  -- Arithmetic operations.
  ADD  _ rd rn o2 -> dst [rd] +++ src [rn] +++ usgOp2 o2
  ADC  _ rd rn o2 -> dst [rd] +++ src [rn] +++ usgOp2 o2
  SUB  _ rd rn o2 -> dst [rd] +++ src [rn] +++ usgOp2 o2
  SBC  _ rd rn o2 -> dst [rd] +++ src [rn] +++ usgOp2 o2
  MUL  _ rd rm rs -> dst [rd] +++ src [rm,rs]
  SDIV _ rd rn rm -> dst [rd] +++ src [rn,rm]
  UDIV _ rd rn rm -> dst [rd] +++ src [rn,rm]
  -- Moves operations.
  MOV  _ rd o2    -> dst [rd]      +++ usgOp2 o2
  MOVS _ rd o2    -> dst [cpsr,rd] +++ usgOp2 o2
  MVN  _ rd o2    -> dst [rd]      +++ usgOp2 o2
  MVNS _ rd o2    -> dst [cpsr,rd] +++ usgOp2 o2
  -- Compare operations.
  CMP  _    rn o2 -> dst [cpsr] +++ src [rn] +++ usgOp2 o2
  CMN  _    rn o2 -> dst [cpsr] +++ src [rn] +++ usgOp2 o2
  -- Logical operations.
  TST  _    rn o2 -> dst [cpsr] +++ src [rn] +++ usgOp2 o2
  TEQ  _    rn o2 -> dst [cpsr] +++ src [rn] +++ usgOp2 o2
  AND  _ rd rn o2 -> dst [rd]   +++ src [rn] +++ usgOp2 o2
  EOR  _ rd rn o2 -> dst [rd]   +++ src [rn] +++ usgOp2 o2
  ORR  _ rd rn o2 -> dst [rd]   +++ src [rn] +++ usgOp2 o2
  ORN  _ rd rn o2 -> dst [rd]   +++ src [rn] +++ usgOp2 o2
  BIC  _ rd rn o2 -> dst [rd]   +++ src [rn] +++ usgOp2 o2
  -- Swap instruction.
  SWP  _ rd rm rn -> dst [rd]   +++ src [rm,rn]
  SWPB _ rd rm rn -> dst [rd]   +++ src [rm,rn]
  -- Software interrupt instruction.
  SWI  _          -> dst []
  -- Jump instructions.
  B   _           -> dst []
  where
    usg   = RU
    src x = usg x []
    dst x = usg [] x
    (+++) (RU s1 d1) (RU s2 d2) = RU (nub $ s1 ++ s2) (nub $ d1 ++ d2)
    regAddr = undefined
    regOp2  = undefined

arm_patchRegsOfInstr :: Instr -> (Reg -> Reg) -> Instr
arm_patchRegsOfInstr instr f = case instr of
  LDR  cd rd ad -> LDR  cd (f rd) (fAd ad)
  LDRB cd rd ad -> LDRB cd (f rd) (fAd ad)
  STR  cd rd ad -> STR  cd (f rd) (fAd ad)
  STRB cd rd ad -> STRB cd (f rd) (fAd ad)
  _             -> panic "arm_patchRegsOfInstr"
  where
    fAd = panic "arm_patchRegsOfInstr fAd"

arm_isJumpishInstr :: Instr -> Bool
arm_isJumpishInstr instr = case instr of
  B _ -> True
  _   -> False

arm_jumpDestOfInstr :: Instr -> [BlockId]
arm_jumpDestOfInstr instr = case instr of
  B label -> [label]
  _       -> []

arm_patchJumpInstr :: Instr -> (BlockId -> BlockId) -> Instr
arm_patchJumpInstr instr f = case instr of
  B label -> B (f label)
  x       -> x

arm_mkSpillInstr :: DynFlags -> Reg -> Int -> Int -> Instr
arm_mkSpillInstr dflags reg delta slot =
  STR AL reg (PreIndexedImmediate sp $ ImmInt $ off - delta)
  where
    off = spillSlotToOffset dflags slot

arm_mkLoadInstr :: DynFlags -> Reg -> Int -> Int -> Instr
arm_mkLoadInstr dflags reg delta slot =
  LDR AL reg (PreIndexedImmediate sp $ ImmInt $ off - delta)
  where
    off = spillSlotToOffset dflags slot

arm_takeDeltaInstr :: Instr -> Maybe Int
arm_takeDeltaInstr instr = case instr of
  _ -> panic "arm_takeDeltaInstr"

arm_isMetaInstr :: Instr -> Bool
arm_isMetaInstr instr = case instr of
  _ -> panic "arm_isMetaInstr"

arm_mkRegRegMoveInstr :: Platform -> Reg -> Reg -> Instr
arm_mkRegRegMoveInstr platform rd rn =
  MOV AL rd (ZeroOffset rn)

arm_takeRegRegMoveInstr :: Instr -> Maybe (Reg, Reg)
arm_takeRegRegMoveInstr instr = case instr of
  MOVE _ rd (ZeroOffset rn) -> Just (rd, rn)
  _                         -> Nothing

arm_mkJumpInstr :: Label -> [Instr]
arm_mkJumpInstr label =
  [B AL label]

arm_mkStackAllocInstr :: Platform -> Int -> Instr
arm_mkStackAllocInstr platform amount =
  SUB AL sp sp (Op2' $ ImmInt amount)

arm_mkStackDeallocInstr :: Platform -> Int -> Instr
arm_mkStackDeallocInstr platform amount =
  ADD AL sp sp (OP2' $ ImmInt amount)
