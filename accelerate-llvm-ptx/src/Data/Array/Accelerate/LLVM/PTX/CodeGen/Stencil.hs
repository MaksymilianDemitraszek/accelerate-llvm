{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Stencil
-- Copyright   : [2018..2020] The Accelerate Team
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Stencil (

  mkStencil1,
  mkStencil2,

) where

import Data.Array.Accelerate.Representation.Array
import Data.Array.Accelerate.Representation.Shape
import Data.Array.Accelerate.Representation.Stencil
import Data.Array.Accelerate.Representation.Type
import Data.Array.Accelerate.Type

-- import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic as AT

import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Stencil
import Data.Array.Accelerate.LLVM.CodeGen.Sugar
import Data.Array.Accelerate.LLVM.Compile.Cache

import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop
import Data.Array.Accelerate.LLVM.PTX.Target                        ( PTX )

import qualified LLVM.AST.Global                                    as LLVM

import Control.Monad
import Data.Array.Accelerate.LLVM.CodeGen.IR (Operands(OP_Unit))
import Data.Array.Accelerate.LLVM.Execute.Async (Async(block))
import Language.Haskell.TH (Code(examineCode))
-- The stencil function is similar to a map, but has access to surrounding
-- elements as specified by the stencil pattern.
--
-- This generates two functions:
--
--  * stencil_inside: does not apply boundary conditions, assumes all element
--                    accesses are valid
--
--  * stencil_border: applies boundary condition check to each array access
--
mkStencil1
    :: UID
    -> Gamma           aenv
    -> StencilR sh a stencil
    -> TypeR b
    -> IRFun1      PTX aenv (stencil -> b)
    -> IRBoundary  PTX aenv (Array sh a)
    -> MIRDelayed  PTX aenv (Array sh a)
    -> CodeGen     PTX      (IROpenAcc PTX aenv (Array sh b))
mkStencil1 uid aenv stencil tp fun bnd marr =
  let repr             = ArrayR shr tp
      (shr, halo)      = stencilHalo stencil
      (arrIn, paramIn) = delayedArray "in" marr
  in
  (+++) <$> mkInside uid aenv repr halo (IRFun1 $ app1 fun <=< stencilAccess stencil Nothing    arrIn) paramIn
        <*> mkBorder uid aenv repr      (IRFun1 $ app1 fun <=< stencilAccess stencil (Just bnd) arrIn) paramIn


mkStencil2
    :: UID
    -> Gamma           aenv
    -> StencilR sh a stencil1
    -> StencilR sh b stencil2
    -> TypeR c
    -> IRFun2      PTX aenv (stencil1 -> stencil2 -> c)
    -> IRBoundary  PTX aenv (Array sh a)
    -> MIRDelayed  PTX aenv (Array sh a)
    -> IRBoundary  PTX aenv (Array sh b)
    -> MIRDelayed  PTX aenv (Array sh b)
    -> CodeGen     PTX      (IROpenAcc PTX aenv (Array sh c))
mkStencil2 uid aenv stencil1 stencil2 tp f bnd1 marr1 bnd2 marr2 =
  let
      repr = ArrayR shr tp
      (arrIn1, paramIn1)  = delayedArray "in1" marr1
      (arrIn2, paramIn2)  = delayedArray "in2" marr2

      inside  = IRFun1 $ \ix -> do
        s1 <- stencilAccess stencil1 Nothing arrIn1 ix
        s2 <- stencilAccess stencil2 Nothing arrIn2 ix
        app2 f s1 s2
      --
      border  = IRFun1 $ \ix -> do
        s1 <- stencilAccess stencil1 (Just bnd1) arrIn1 ix
        s2 <- stencilAccess stencil2 (Just bnd2) arrIn2 ix
        app2 f s1 s2

      (shr, halo1) = stencilHalo stencil1
      (_,   halo2) = stencilHalo stencil2
      halo         = union shr halo1 halo2
  in
  (+++) <$> mkInside uid aenv repr halo inside (paramIn1 ++ paramIn2)
        <*> mkBorder uid aenv repr      border (paramIn1 ++ paramIn2)

mkInside = mkInsideNaive

mkInsideNaive
    :: UID
    -> Gamma aenv
    -> ArrayR (Array sh e)
    -> sh
    -> IRFun1  PTX aenv (sh -> e)
    -> [LLVM.Parameter]
    -> CodeGen PTX      (IROpenAcc PTX aenv (Array sh e))
mkInsideNaive uid aenv repr@(ArrayR shr _) halo apply paramIn =
  let
      (arrOut, paramOut)  = mutableArray repr "out"
      paramInside         = parameter    (shapeType shr) "shInside"
      shInside            = local        (shapeType shr) "shInside"
      shOut               = irArrayShape arrOut
      paramEnv            = envParam aenv
  in
  makeOpenAcc uid "stencil_inside" (paramInside ++ paramOut ++ paramIn ++ paramEnv) $ do

    start <- return (liftInt 0)
    end   <- shapeSize shr shInside

    -- iterate over the inside region as a linear index space
    --
    imapFromTo start end $ \i -> do
      ixIn  <- indexOfInt shr shInside i                    -- convert to multidimensional index of inside region
      ixOut <- offset shr ixIn (lift (shapeType shr) halo)  -- shift to multidimensional index of outside region
      r     <- app1 apply ixOut                             -- apply generator function
      j     <- intOfIndex shr shOut ixOut
      writeArray TypeInt arrOut j r

    return_


mkInsideCB
    :: UID
    -> Gamma aenv
    -> ArrayR (Array sh e)
    -> sh
    -> IRFun1  PTX aenv (sh -> e)
    -> [LLVM.Parameter]
    -> CodeGen PTX      (IROpenAcc PTX aenv (Array sh e))
mkInsideCB uid aenv repr@(ArrayR shr _) halo apply paramIn =
  let
      (arrOut, paramOut)  = mutableArray repr "out"
      paramInside         = parameter    (shapeType shr) "shInside"
      shInside            = local        (shapeType shr) "shInside"
      shOut               = irArrayShape arrOut
      paramEnv            = envParam aenv
  in
  makeOpenAcc uid "stencil_inside" (paramInside ++ paramOut ++ paramIn ++ paramEnv) $ do

    start <- return (liftInt 0)
    end   <- shapeSize shr shInside

    -- -- Column Based Iteration
    columnWidth <- return $ liftInt 32

    inputWidth  <- widthOp shr shInside
    inputHeight <- heightOp shr shInside

    columnSize  <- mul numType columnWidth inputHeight
    
    inputExtraCol <- add numType end columnSize
    inputExtraColOf <- sub numType inputExtraCol (liftInt 1)
    columnCount <- AT.quot integralType inputExtraColOf columnSize
    columnLastIndex <- sub numType columnCount (liftInt 1)

    multp <- mul numType columnLastIndex columnWidth
    lastColWidth <- sub numType inputWidth multp
    -- Column Based Iteration

    -- iterate over the inside region as a linear index space
    --
    -- (ShapeRsnoc (ShapeRsnoc ShapeRz)) columnWidth inputWidth columnSize columnCount idx
    imapFromTo start end $ \i -> do
      -- ixIn    <- mapToCB shr columnWidth input_width columnSize i  -- convert to multidimensional index of inside region
      ixIn    <- mapToColumn shr columnWidth columnSize columnLastIndex lastColWidth i  -- convert to multidimensional index of inside region
      ixOut <- offset shr ixIn (lift (shapeType shr) halo)  -- shift to multidimensional index of outside region
      r     <- app1 apply ixOut                             -- apply generator function
      j     <- intOfIndex shr shOut ixOut
      writeArray TypeInt arrOut j r

    return_


mapToColumn :: ShapeR sh -> Operands Int -> Operands Int -> Operands Int -> Operands Int -> Operands Int -> CodeGen arch (Operands sh)
mapToColumn (ShapeRsnoc (ShapeRsnoc ShapeRz)) columnWidth columnSize columnLastIndex lastColWidth idx = do
    column_index      <- AT.quot integralType idx columnSize
    column_offset     <- mul numType column_index columnWidth
    idx' <- AT.rem integralType idx columnSize
    let idxEq = AT.eq singleType column_index columnLastIndex

    column_current_width <- ifThenElse (TupRsingle $ SingleScalarType $ NumSingleType (numType @Int),
        idxEq
      ) ( do
        return lastColWidth
      ) ( do
        return columnWidth
      )

    x_in_column <- AT.rem integralType idx' column_current_width
    x <- add numType column_offset x_in_column
    y <- AT.quot integralType idx' column_current_width
    return $ OP_Pair (OP_Pair OP_Unit y) x
mapToColumn _ _ _ _ _ _ = error "not allowed"


widthOp :: ShapeR sh -> Operands sh -> CodeGen arch (Operands Int)
widthOp ShapeRz OP_Unit
  = return $ liftInt 0
widthOp (ShapeRsnoc ShapeRz) (OP_Pair _ w)
  = return w
widthOp (ShapeRsnoc d) (OP_Pair x _)
  = widthOp d x


heightOp :: ShapeR sh -> Operands sh -> CodeGen arch (Operands Int)
heightOp ShapeRz OP_Unit
  = return $ liftInt 0
heightOp (ShapeRsnoc (ShapeRsnoc ShapeRz)) (OP_Pair (OP_Pair _ _) h)
  = return h
heightOp (ShapeRsnoc d) (OP_Pair x _)
  = widthOp d x


mapToCB :: ShapeR sh -> Operands Int -> Operands Int -> Operands Int -> Operands Int -> CodeGen arch (Operands sh)
mapToCB (ShapeRsnoc (ShapeRsnoc ShapeRz)) columnWidth inputWidth columnSize idx = do
    colId      <- AT.quot integralType idx columnSize
    colTid     <- AT.rem integralType  idx columnSize

    colOff     <- mul numType colId columnWidth

    rightOff <- sub numType inputWidth colOff
    diff <- sub numType rightOff columnWidth
    
    colTw <- ifThenElse (
      TupRsingle $ SingleScalarType $ NumSingleType (numType @Int),
      AT.gte singleType diff (liftInt 0)
      ) 
      (return columnWidth)
      (return rightOff)
    
    xInColumn <- AT.rem integralType colTid colTw
    x <- add numType xInColumn colOff
    y <- AT.quot integralType colTid colTw
    return $ OP_Pair (OP_Pair OP_Unit y) x
mapToCB _ columnWidth inputWidth columnSize idx = error "not allowed"



-- mkInsideEB
--     :: UID
--     -> Gamma aenv
--     -> ArrayR (Array sh e)
--     -> sh
--     -> IRFun1  PTX aenv (sh -> e)
--     -> [LLVM.Parameter]
--     -> CodeGen PTX      (IROpenAcc PTX aenv (Array sh e))
-- mkInsideEB uid aenv repr@(ArrayR shr _) halo apply paramIn =
--   let
--       (arrOut, paramOut)  = mutableArray repr "out"
--       paramInside         = parameter    (shapeType shr) "shInside"
--       shInside            = local        (shapeType shr) "shInside"
--       shOut               = irArrayShape arrOut
--       paramEnv            = envParam aenv
--   in
--   makeOpenAcc uid "stencil_inside" (paramInside ++ paramOut ++ paramIn ++ paramEnv) $ do

--     start <- return (liftInt 0)
--     end   <- shapeSize shr shInside

--     -- Emulated Blocks
--     inputWidth  <- widthOp shr shInside
--     inputHeight <- AT.quot integralType end inputWidth

--     -- gridDimE <- AT.fromIntegral integralType numType =<< gridDim
--     bDimOrg <- AT.fromIntegral integralType numType =<< blockDim
--     -- orgBlockIdX <- AT.fromIntegral integralType numType =<< blockIdx
--     tIdXOrg <- AT.fromIntegral integralType numType =<< threadIdx

--     let blockDimY = liftInt 8 
--     blockDimX <- AT.quot integralType bDimOrg blockDimY
--     numOfBlocksRow <- AT.quot integralType inputWidth blockDimX 

--     threadIdX <- AT.rem integralType tIdXOrg blockDimX
--     threadIdY <- AT.quot integralType tIdXOrg blockDimX

--     extra <- calcExtra inputWidth inputHeight blockDimX blockDimY
--     end' <- AT.add numType end extra

--     -- Emulated Block

--     -- iterate over the inside region as a linear index space
--     --
--     imapFromTo start end' $ \i -> do
--       bIdX <- AT.quot integralType i bDimOrg
--       ixIn    <- mapToEB shr bIdX numOfBlocksRow blockDimX blockDimY threadIdX threadIdY
--       AT.when (isInside shr ixIn inputWidth inputHeight) (do
--         ixOut <- offset shr ixIn (lift (shapeType shr) halo)  -- shift to multidimensional index of outside region
--         r     <- app1 apply ixOut                             -- apply generator function
--         j     <- intOfIndex shr shOut ixOut
--         writeArray TypeInt arrOut j r
--         )
--     return_

-- isInside :: ShapeR sh -> Operands sh -> Operands Int -> Operands Int -> CodeGen arch (Operands Bool)
-- isInside (ShapeRsnoc (ShapeRsnoc ShapeRz)) (OP_Pair (OP_Pair OP_Unit y) x) inputWidth inputHeight = do
--   l <- AT.lt singleType y inputHeight
--   r <-AT.lt singleType x inputWidth
--   AT.land l r 
-- isInside _ _ _ _ = error "not supported"

-- calcExtra :: IsIntegral a => Operands a -> Operands a -> Operands a -> Operands a -> CodeGen arch (Operands a)
-- calcExtra inputWidth inputHeight blockDimX blockDimY = do
--     haloXOff <- AT.rem integralType inputWidth blockDimX
--     haloX <- AT.sub numType inputWidth haloXOff 
--     haloYOff <- AT.rem integralType inputWidth blockDimY
--     haloY <- AT.sub numType inputWidth haloYOff 

--     a <- AT.mul numType haloX inputHeight
--     b <- AT.mul numType haloY inputWidth
--     c <- AT.mul numType haloY haloX 
--     d <- AT.add numType a b
--     AT.sub numType d c


-- mapToEB :: ShapeR sh -> Operands Int -> Operands Int -> Operands Int -> Operands Int ->  Operands Int -> Operands Int -> CodeGen arch (Operands sh)
-- mapToEB (ShapeRsnoc (ShapeRsnoc ShapeRz)) orgBlockIdX numOfBlocksRow blockDimX blockDimY threadIdX threadIdY = do
--     blockIdX <- AT.rem integralType orgBlockIdX numOfBlocksRow  
--     blockIdY <- AT.quot integralType orgBlockIdX numOfBlocksRow  
--     xOff <- AT.mul numType blockDimX blockIdX
--     x <- AT.add numType xOff threadIdX 
--     yOff <- AT.mul numType blockDimY blockIdY
--     y <- AT.add numType yOff threadIdY 
--     return $ OP_Pair (OP_Pair OP_Unit y) x
-- mapToEB _ _ _ _ _ _ _ = error "not supported"



mkBorder
    :: UID
    -> Gamma aenv
    -> ArrayR (Array sh e)
    -> IRFun1  PTX aenv (sh -> e)
    -> [LLVM.Parameter]
    -> CodeGen PTX      (IROpenAcc PTX aenv (Array sh e))
mkBorder uid aenv repr@(ArrayR shr _) apply paramIn =
  let
      (arrOut, paramOut)  = mutableArray repr "out"
      paramFrom           = parameter    (shapeType shr) "shFrom"
      shFrom              = local        (shapeType shr) "shFrom"
      paramInside         = parameter    (shapeType shr) "shInside"
      shInside            = local        (shapeType shr) "shInside"
      shOut               = irArrayShape arrOut
      paramEnv            = envParam aenv
  in
  makeOpenAcc uid "stencil_border" (paramFrom ++ paramInside ++ paramOut ++ paramIn ++ paramEnv) $ do

    start <- return (liftInt 0)
    end   <- shapeSize shr shInside

    imapFromTo start end $ \i -> do

      ixIn  <- indexOfInt shr shInside i    -- convert to multidimensional index of inside region
      ixOut <- offset shr ixIn shFrom       -- shift to multidimensional index of outside region
      r     <- app1 apply ixOut             -- apply generator function
      j     <- intOfIndex shr shOut ixOut
      writeArray TypeInt arrOut j r

    return_


offset :: ShapeR sh -> Operands sh -> Operands sh -> CodeGen PTX (Operands sh)
offset shr sh1 sh2 = go shr sh1 sh2
  where
    go :: ShapeR t -> Operands t -> Operands t -> CodeGen PTX (Operands t)
    go ShapeRz OP_Unit OP_Unit
      = return OP_Unit

    go (ShapeRsnoc t) (OP_Pair sa1 sb1) (OP_Pair sa2 sb2)
      = do x <- add (numType :: NumType Int) sb1 sb2
           OP_Pair <$> go t sa1 sa2 <*> return x

