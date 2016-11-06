{-# OPTIONS_GHC -w #-}
{-# OPTIONS -cpp #-}
module Outer.Parser where
  
import Outer.Lexer
import Common.Error
import Common.SrcLoc
import Outer.ParseMonad
import Outer.AST 
import Common.Types

import Control.Monad.Error

import Debug.Trace
import qualified Data.Array as Happy_Data_Array
import qualified System.IO as Happy_System_IO
import qualified System.IO.Unsafe as Happy_System_IO_Unsafe
import qualified Debug.Trace as Happy_Debug_Trace
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.19.5

data HappyAbsSyn 
	= HappyTerminal ((Located Token))
	| HappyErrorToken Int
	| HappyAbsSyn5 (Prg)
	| HappyAbsSyn6 ([Decl])
	| HappyAbsSyn7 (Decl)
	| HappyAbsSyn9 ([ConDecl])
	| HappyAbsSyn10 (ConDecl)
	| HappyAbsSyn11 (OTcType)
	| HappyAbsSyn12 ([OTcType])
	| HappyAbsSyn14 (TyConId)
	| HappyAbsSyn18 ([VarId])
	| HappyAbsSyn19 (Exp)
	| HappyAbsSyn21 ([Exp])
	| HappyAbsSyn25 ([Alt])
	| HappyAbsSyn26 (Alt)
	| HappyAbsSyn27 (Pat)
	| HappyAbsSyn29 ([Pat])

happyActOffsets :: Happy_Data_Array.Array Int Int
happyActOffsets = Happy_Data_Array.listArray (0,204) ([46,550,46,0,550,487,481,402,550,0,0,429,0,0,550,550,429,462,53,16,0,550,46,435,46,385,46,452,550,0,550,0,445,409,0,0,0,550,0,550,0,0,0,0,431,0,333,0,0,550,59,318,0,0,0,0,431,431,431,46,499,431,401,368,360,346,431,431,431,0,0,0,431,348,397,330,298,1,0,0,491,0,483,464,0,309,280,243,322,0,0,-6,294,363,306,363,363,363,363,363,363,363,363,363,363,363,363,363,59,0,0,0,480,480,480,480,480,480,206,261,0,0,596,596,318,0,227,0,0,363,0,245,363,594,282,0,0,11,274,477,0,0,363,471,363,363,190,246,235,174,363,550,363,0,10,137,215,120,0,0,0,471,0,318,229,180,119,0,151,202,-23,216,129,0,0,0,363,363,0,100,145,153,363,0,318,318,471,471,363,363,63,318,-26,-28,47,135,363,363,363,153,318,318,363,318,0
	])

happyGotoOffsets :: Happy_Data_Array.Array Int Int
happyGotoOffsets = Happy_Data_Array.listArray (0,204) ([622,535,132,0,4,99,54,0,612,0,0,0,0,0,523,502,0,0,0,0,0,434,128,64,26,0,13,0,109,0,400,0,0,3,0,0,0,366,0,339,0,0,0,0,604,0,0,0,0,378,136,0,0,0,0,0,57,521,602,8,592,597,0,0,0,0,595,593,591,0,0,0,589,0,587,0,0,0,0,0,576,0,395,234,0,0,0,0,0,0,0,0,0,583,0,581,579,577,575,573,571,569,567,565,563,561,559,555,112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,533,0,551,553,0,0,0,0,0,0,542,0,0,549,527,547,545,0,0,0,0,504,386,448,0,0,0,0,0,0,0,0,181,0,0,0,440,432,0,0,0,0,0,0,0,0,0,437,414,0,0,0,0,405,0,0,0,404,290,285,208,0,0,0,0,0,0,155,105,81,0,0,0,65,0,0
	])

happyDefActions :: Happy_Data_Array.Array Int Int
happyDefActions = Happy_Data_Array.listArray (0,204) ([-4,0,0,-3,0,0,0,-25,-13,-15,-16,0,-17,-21,0,0,0,0,0,0,-14,0,-4,0,-4,0,-4,0,0,-5,0,-7,0,-27,-6,-24,-20,0,-18,0,-19,-22,-23,-28,0,-8,-9,-10,-12,0,-36,-26,-29,-31,-30,-32,0,-67,0,-4,0,0,0,0,0,0,0,0,0,-39,-38,-40,0,0,0,0,0,0,-77,-81,-82,-83,0,0,-80,0,0,-69,0,-68,-70,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,-65,-37,-11,-66,-53,-52,-51,-50,-49,-48,-47,-45,-44,-43,-42,-41,-54,-62,0,-34,-33,0,-35,0,0,-90,0,-91,-86,0,0,-88,-78,-82,0,0,0,0,0,-29,0,0,0,0,0,-59,0,0,-79,0,-89,-85,-84,0,-87,-56,0,-72,0,-71,0,0,0,0,-81,-73,-55,-92,0,0,-63,0,0,-64,0,-60,-58,-57,0,0,0,0,0,-74,0,0,0,0,0,0,0,-46,-76,-75,0,-61
	])

happyCheck :: Happy_Data_Array.Array Int Int
happyCheck = Happy_Data_Array.listArray (0,671) ([-1,7,1,31,10,31,12,3,31,1,6,7,8,9,1,11,13,7,7,47,10,47,12,7,47,31,32,1,34,35,36,37,31,39,40,41,42,43,44,45,46,31,31,32,34,35,36,37,32,39,40,41,42,43,44,45,46,10,11,12,7,2,3,4,5,6,12,8,22,23,24,14,15,10,11,12,19,13,31,14,15,34,35,36,37,32,39,40,41,42,43,44,45,46,31,14,15,34,35,36,37,2,39,40,41,42,43,44,45,46,10,11,12,4,5,6,7,8,9,14,15,2,3,4,5,6,14,8,16,1,10,31,12,1,34,35,36,37,18,39,40,41,42,43,44,45,46,10,29,12,14,31,16,18,34,35,36,37,21,39,40,41,42,43,44,45,46,38,31,14,15,34,35,36,37,30,39,40,41,42,43,44,45,46,10,11,12,34,35,36,37,40,39,40,41,42,43,44,45,46,10,11,12,22,23,31,25,26,34,35,36,37,10,39,40,41,42,43,44,45,46,31,14,15,34,35,36,37,48,39,40,41,42,43,44,45,46,10,11,12,34,35,36,37,15,39,31,41,42,43,44,45,46,10,38,12,22,23,31,25,26,34,35,36,37,30,39,40,41,42,43,44,45,46,31,32,30,34,35,36,37,7,39,40,41,42,43,44,45,46,10,9,12,48,14,34,35,36,37,14,15,7,41,42,43,44,45,46,10,3,12,31,22,23,34,35,36,37,20,39,40,41,42,43,44,45,46,18,10,31,12,9,34,35,36,37,6,39,40,41,42,43,44,45,46,6,7,8,9,31,11,3,34,35,36,37,10,39,40,41,42,43,44,45,46,2,3,4,5,6,10,8,6,7,8,9,13,11,10,16,17,48,19,5,6,7,8,9,25,26,27,28,6,7,8,9,33,34,35,2,3,4,5,6,3,8,6,7,8,9,13,11,3,16,17,30,19,22,23,14,15,26,25,26,27,28,22,23,14,15,33,34,35,2,3,4,5,6,3,8,6,7,8,9,13,11,1,16,17,47,19,14,15,1,22,23,25,26,27,28,20,21,14,15,33,34,35,3,4,5,6,9,8,9,3,4,5,6,49,8,3,4,5,6,3,8,3,4,5,6,3,8,-1,29,3,4,5,6,-1,8,29,-1,3,4,5,6,29,8,6,7,8,9,29,11,34,35,36,37,14,15,29,41,42,43,44,45,46,-1,29,6,7,8,9,10,11,14,15,-1,17,18,19,6,7,8,9,-1,11,14,15,22,23,18,19,3,4,-1,6,-1,8,14,15,14,15,14,15,23,24,14,15,14,15,20,21,14,15,14,15,14,15,14,15,14,15,14,15,14,15,14,15,14,15,14,15,14,15,14,15,14,15,23,24,14,15,14,15,14,15,14,15,14,15,14,15,-1,22,23,14,15,14,15,8,9,0,1,-1,31,32,-1,-1,-1,-1,-1,36,37,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1
	])

happyTable :: Happy_Data_Array.Array Int Int
happyTable = Happy_Data_Array.listArray (0,671) ([0,129,143,144,94,144,95,26,144,85,7,8,9,10,29,27,43,179,161,197,94,198,95,37,189,96,130,31,97,98,99,100,144,101,102,103,104,105,106,107,108,96,144,162,97,98,99,100,38,101,102,103,104,105,106,107,108,94,196,95,39,53,54,55,56,57,22,58,5,6,7,50,91,94,199,95,92,32,96,50,203,97,98,99,100,40,101,102,103,104,105,106,107,108,96,50,199,97,98,99,100,24,101,102,103,104,105,106,107,108,94,184,95,46,47,48,8,9,10,50,200,172,173,81,82,83,108,84,111,34,94,96,95,3,97,98,99,100,177,101,102,103,104,105,106,107,108,94,85,95,108,96,109,203,97,98,99,100,178,101,102,103,104,105,106,107,108,187,96,50,201,97,98,99,100,183,101,102,103,104,105,106,107,108,94,151,95,97,98,99,100,170,101,102,103,104,105,106,107,108,94,154,95,133,78,96,175,135,97,98,99,100,190,101,102,103,104,105,106,107,108,96,50,190,97,98,99,100,167,101,102,103,104,105,106,107,108,94,169,95,97,98,99,100,175,101,144,103,104,105,106,107,108,94,188,95,133,78,96,134,135,97,98,99,100,152,101,102,103,104,105,106,107,108,96,130,153,97,98,99,100,160,101,102,103,104,105,106,107,108,94,163,95,167,132,97,98,99,100,50,191,128,103,104,105,106,107,108,94,126,95,96,192,78,97,98,99,100,145,101,102,103,104,105,106,107,108,133,94,96,95,131,97,98,99,100,146,101,102,103,104,105,106,107,108,7,8,9,10,96,41,149,97,98,99,100,73,101,102,103,104,105,106,107,108,53,54,55,56,57,74,58,7,8,9,10,59,42,75,60,61,50,62,110,48,8,9,10,63,64,65,66,180,8,9,10,67,68,69,148,54,55,56,57,76,58,7,8,9,10,59,45,34,60,61,31,62,137,78,50,194,138,63,64,65,66,193,78,50,184,67,68,69,53,54,55,56,57,34,58,7,8,9,10,59,35,45,60,61,22,62,50,185,29,170,78,63,64,65,66,173,165,50,179,67,68,69,80,81,82,83,41,84,137,80,81,82,83,-1,84,80,142,82,83,24,84,80,81,82,83,26,84,0,85,80,142,82,83,0,84,85,0,80,81,82,83,85,84,7,8,9,10,85,17,97,98,99,100,50,181,85,0,0,0,0,0,0,0,85,7,8,9,10,18,19,50,87,0,88,89,90,7,8,9,10,0,11,50,87,156,78,167,90,13,14,0,15,0,16,50,154,50,155,50,157,139,158,50,163,50,112,164,165,50,113,50,114,50,115,50,116,50,117,50,118,50,119,50,120,50,121,50,122,50,123,50,124,50,126,139,140,50,146,50,149,50,69,50,70,50,71,50,76,0,77,78,50,86,50,51,20,10,16,3,0,144,162,0,0,0,0,0,99,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
	])

happyReduceArr = Happy_Data_Array.array (2, 91) [
	(2 , happyReduce_2),
	(3 , happyReduce_3),
	(4 , happyReduce_4),
	(5 , happyReduce_5),
	(6 , happyReduce_6),
	(7 , happyReduce_7),
	(8 , happyReduce_8),
	(9 , happyReduce_9),
	(10 , happyReduce_10),
	(11 , happyReduce_11),
	(12 , happyReduce_12),
	(13 , happyReduce_13),
	(14 , happyReduce_14),
	(15 , happyReduce_15),
	(16 , happyReduce_16),
	(17 , happyReduce_17),
	(18 , happyReduce_18),
	(19 , happyReduce_19),
	(20 , happyReduce_20),
	(21 , happyReduce_21),
	(22 , happyReduce_22),
	(23 , happyReduce_23),
	(24 , happyReduce_24),
	(25 , happyReduce_25),
	(26 , happyReduce_26),
	(27 , happyReduce_27),
	(28 , happyReduce_28),
	(29 , happyReduce_29),
	(30 , happyReduce_30),
	(31 , happyReduce_31),
	(32 , happyReduce_32),
	(33 , happyReduce_33),
	(34 , happyReduce_34),
	(35 , happyReduce_35),
	(36 , happyReduce_36),
	(37 , happyReduce_37),
	(38 , happyReduce_38),
	(39 , happyReduce_39),
	(40 , happyReduce_40),
	(41 , happyReduce_41),
	(42 , happyReduce_42),
	(43 , happyReduce_43),
	(44 , happyReduce_44),
	(45 , happyReduce_45),
	(46 , happyReduce_46),
	(47 , happyReduce_47),
	(48 , happyReduce_48),
	(49 , happyReduce_49),
	(50 , happyReduce_50),
	(51 , happyReduce_51),
	(52 , happyReduce_52),
	(53 , happyReduce_53),
	(54 , happyReduce_54),
	(55 , happyReduce_55),
	(56 , happyReduce_56),
	(57 , happyReduce_57),
	(58 , happyReduce_58),
	(59 , happyReduce_59),
	(60 , happyReduce_60),
	(61 , happyReduce_61),
	(62 , happyReduce_62),
	(63 , happyReduce_63),
	(64 , happyReduce_64),
	(65 , happyReduce_65),
	(66 , happyReduce_66),
	(67 , happyReduce_67),
	(68 , happyReduce_68),
	(69 , happyReduce_69),
	(70 , happyReduce_70),
	(71 , happyReduce_71),
	(72 , happyReduce_72),
	(73 , happyReduce_73),
	(74 , happyReduce_74),
	(75 , happyReduce_75),
	(76 , happyReduce_76),
	(77 , happyReduce_77),
	(78 , happyReduce_78),
	(79 , happyReduce_79),
	(80 , happyReduce_80),
	(81 , happyReduce_81),
	(82 , happyReduce_82),
	(83 , happyReduce_83),
	(84 , happyReduce_84),
	(85 , happyReduce_85),
	(86 , happyReduce_86),
	(87 , happyReduce_87),
	(88 , happyReduce_88),
	(89 , happyReduce_89),
	(90 , happyReduce_90),
	(91 , happyReduce_91)
	]

happy_n_terms = 50 :: Int
happy_n_nonterms = 27 :: Int

happyReduce_2 = happyMonadReduce 1 0 happyReduction_2
happyReduction_2 ((HappyAbsSyn6  happy_var_1) `HappyStk`
	happyRest) tk
	 = happyThen (( checkRevDecls happy_var_1)
	) (\r -> happyReturn (HappyAbsSyn5 r))

happyReduce_3 = happySpecReduce_0  1 happyReduction_3
happyReduction_3  =  HappyAbsSyn6
		 ([]
	)

happyReduce_4 = happySpecReduce_3  1 happyReduction_4
happyReduction_4 (HappyAbsSyn6  happy_var_3)
	(HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn6
		 (happy_var_2 : happy_var_3
	)
happyReduction_4 _ _ _  = notHappyAtAll 

happyReduce_5 = happySpecReduce_3  1 happyReduction_5
happyReduction_5 (HappyAbsSyn6  happy_var_3)
	(HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn6
		 (happy_var_2 : happy_var_3
	)
happyReduction_5 _ _ _  = notHappyAtAll 

happyReduce_6 = happySpecReduce_3  1 happyReduction_6
happyReduction_6 (HappyAbsSyn6  happy_var_3)
	(HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn6
		 (happy_var_2 : happy_var_3
	)
happyReduction_6 _ _ _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_3  2 happyReduction_7
happyReduction_7 (HappyAbsSyn11  happy_var_3)
	_
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn7
		 (TypeSig (getLoc happy_var_1) (unVARID happy_var_1) happy_var_3
	)
happyReduction_7 _ _ _  = notHappyAtAll 

happyReduce_8 = happyMonadReduce 3 3 happyReduction_8
happyReduction_8 ((HappyAbsSyn9  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_1) `HappyStk`
	happyRest) tk
	 = happyThen (( do { (c,ts) <- checkDataHeader happy_var_1
                              ; l <- getSrcLoc 
                              ; return $ DataDecl l c ts (reverse happy_var_3) })
	) (\r -> happyReturn (HappyAbsSyn7 r))

happyReduce_9 = happySpecReduce_1  4 happyReduction_9
happyReduction_9 (HappyAbsSyn10  happy_var_1)
	 =  HappyAbsSyn9
		 ([happy_var_1]
	)
happyReduction_9 _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_3  4 happyReduction_10
happyReduction_10 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn9
		 (happy_var_3 : happy_var_1
	)
happyReduction_10 _ _ _  = notHappyAtAll 

happyReduce_11 = happyMonadReduce 1 5 happyReduction_11
happyReduction_11 ((HappyAbsSyn11  happy_var_1) `HappyStk`
	happyRest) tk
	 = happyThen (( mkConDecl happy_var_1)
	) (\r -> happyReturn (HappyAbsSyn10 r))

happyReduce_12 = happySpecReduce_1  6 happyReduction_12
happyReduction_12 (HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn11
		 (fixConType (reverse happy_var_1)
	)
happyReduction_12 _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_2  7 happyReduction_13
happyReduction_13 (HappyAbsSyn11  happy_var_2)
	(HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn12
		 (happy_var_2 : happy_var_1
	)
happyReduction_13 _ _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_1  7 happyReduction_14
happyReduction_14 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn12
		 ([happy_var_1]
	)
happyReduction_14 _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_1  8 happyReduction_15
happyReduction_15 (HappyAbsSyn14  happy_var_1)
	 =  HappyAbsSyn11
		 (TcCon happy_var_1 0 []
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_1  8 happyReduction_16
happyReduction_16 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn11
		 (TcVar (unVARID happy_var_1)
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_3  8 happyReduction_17
happyReduction_17 _
	(HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (let n = length happy_var_2 in 
                                TcCon (tuple_tycon_name n) n (reverse happy_var_2)
	)
happyReduction_17 _ _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_3  8 happyReduction_18
happyReduction_18 _
	(HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (TcCon list_tycon_name 1 [happy_var_2]
	)
happyReduction_18 _ _ _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_3  8 happyReduction_19
happyReduction_19 _
	(HappyAbsSyn11  happy_var_2)
	_
	 =  HappyAbsSyn11
		 (happy_var_2
	)
happyReduction_19 _ _ _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  9 happyReduction_20
happyReduction_20 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn14
		 (unCONID happy_var_1
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_3  10 happyReduction_21
happyReduction_21 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn12
		 (happy_var_3 : happy_var_1
	)
happyReduction_21 _ _ _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_3  10 happyReduction_22
happyReduction_22 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn12
		 ([happy_var_3, happy_var_1]
	)
happyReduction_22 _ _ _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_3  11 happyReduction_23
happyReduction_23 (HappyAbsSyn11  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (TcFun happy_var_1 happy_var_3
	)
happyReduction_23 _ _ _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_1  11 happyReduction_24
happyReduction_24 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_24 _  = notHappyAtAll 

happyReduce_25 = happyMonadReduce 4 12 happyReduction_25
happyReduction_25 ((HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn18  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest) tk
	 = happyThen (( do { l <- getSrcLoc
                                    ; checkValDef l (unVARID happy_var_1) happy_var_2 happy_var_4 })
	) (\r -> happyReturn (HappyAbsSyn7 r))

happyReduce_26 = happySpecReduce_1  13 happyReduction_26
happyReduction_26 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn18
		 ([unVARID happy_var_1]
	)
happyReduction_26 _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_2  13 happyReduction_27
happyReduction_27 (HappyAbsSyn18  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn18
		 ((unVARID happy_var_1) : happy_var_2
	)
happyReduction_27 _ _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_1  14 happyReduction_28
happyReduction_28 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn19
		 (Lit . LitInt $ unINT happy_var_1
	)
happyReduction_28 _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_1  14 happyReduction_29
happyReduction_29 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn19
		 (Con $ unCONID happy_var_1
	)
happyReduction_29 _  = notHappyAtAll 

happyReduce_30 = happySpecReduce_1  14 happyReduction_30
happyReduction_30 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn19
		 (Var $ unVARID happy_var_1
	)
happyReduction_30 _  = notHappyAtAll 

happyReduce_31 = happySpecReduce_1  14 happyReduction_31
happyReduction_31 _
	 =  HappyAbsSyn19
		 (Con "()"
	)

happyReduce_32 = happySpecReduce_3  14 happyReduction_32
happyReduction_32 _
	(HappyAbsSyn19  happy_var_2)
	_
	 =  HappyAbsSyn19
		 (happy_var_2
	)
happyReduction_32 _ _ _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_3  14 happyReduction_33
happyReduction_33 _
	(HappyAbsSyn21  happy_var_2)
	_
	 =  HappyAbsSyn19
		 (appify (Con $ tuple_con_name $ length happy_var_2) happy_var_2
	)
happyReduction_33 _ _ _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_3  14 happyReduction_34
happyReduction_34 _
	(HappyAbsSyn21  happy_var_2)
	_
	 =  HappyAbsSyn19
		 (listify happy_var_2
	)
happyReduction_34 _ _ _  = notHappyAtAll 

happyReduce_35 = happySpecReduce_1  15 happyReduction_35
happyReduction_35 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (happy_var_1
	)
happyReduction_35 _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_2  15 happyReduction_36
happyReduction_36 (HappyAbsSyn21  happy_var_2)
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (appify happy_var_1 happy_var_2
	)
happyReduction_36 _ _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_2  15 happyReduction_37
happyReduction_37 (HappyAbsSyn19  happy_var_2)
	_
	 =  HappyAbsSyn19
		 (happy_var_2
	)
happyReduction_37 _ _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_2  15 happyReduction_38
happyReduction_38 (HappyAbsSyn19  happy_var_2)
	_
	 =  HappyAbsSyn19
		 (Unop OpNeg happy_var_2
	)
happyReduction_38 _ _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_2  15 happyReduction_39
happyReduction_39 (HappyAbsSyn19  happy_var_2)
	_
	 =  HappyAbsSyn19
		 (Unop OpNot happy_var_2
	)
happyReduction_39 _ _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_3  15 happyReduction_40
happyReduction_40 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Binop happy_var_1 OpPlus happy_var_3
	)
happyReduction_40 _ _ _  = notHappyAtAll 

happyReduce_41 = happySpecReduce_3  15 happyReduction_41
happyReduction_41 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Binop happy_var_1 OpMinus happy_var_3
	)
happyReduction_41 _ _ _  = notHappyAtAll 

happyReduce_42 = happySpecReduce_3  15 happyReduction_42
happyReduction_42 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Binop happy_var_1 OpTimes happy_var_3
	)
happyReduction_42 _ _ _  = notHappyAtAll 

happyReduce_43 = happySpecReduce_3  15 happyReduction_43
happyReduction_43 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Binop happy_var_1 OpDiv happy_var_3
	)
happyReduction_43 _ _ _  = notHappyAtAll 

happyReduce_44 = happySpecReduce_3  15 happyReduction_44
happyReduction_44 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Conj happy_var_1 happy_var_3
	)
happyReduction_44 _ _ _  = notHappyAtAll 

happyReduce_45 = happyReduce 9 15 happyReduction_45
happyReduction_45 ((HappyAbsSyn19  happy_var_9) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_7) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Disj (Just happy_var_3) happy_var_1 (Just happy_var_7) happy_var_9
	) `HappyStk` happyRest

happyReduce_46 = happySpecReduce_3  15 happyReduction_46
happyReduction_46 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Disj Nothing happy_var_1 Nothing happy_var_3
	)
happyReduction_46 _ _ _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_3  15 happyReduction_47
happyReduction_47 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Binop happy_var_1 OpEq happy_var_3
	)
happyReduction_47 _ _ _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_3  15 happyReduction_48
happyReduction_48 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Binop happy_var_1 OpNe happy_var_3
	)
happyReduction_48 _ _ _  = notHappyAtAll 

happyReduce_49 = happySpecReduce_3  15 happyReduction_49
happyReduction_49 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Binop happy_var_1 OpLt happy_var_3
	)
happyReduction_49 _ _ _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_3  15 happyReduction_50
happyReduction_50 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Binop happy_var_1 OpGt happy_var_3
	)
happyReduction_50 _ _ _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_3  15 happyReduction_51
happyReduction_51 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Binop happy_var_1 OpLe happy_var_3
	)
happyReduction_51 _ _ _  = notHappyAtAll 

happyReduce_52 = happySpecReduce_3  15 happyReduction_52
happyReduction_52 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Binop happy_var_1 OpGe happy_var_3
	)
happyReduction_52 _ _ _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_3  15 happyReduction_53
happyReduction_53 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (App (App (Con cons_con_name) happy_var_1) happy_var_3
	)
happyReduction_53 _ _ _  = notHappyAtAll 

happyReduce_54 = happyReduce 5 15 happyReduction_54
happyReduction_54 (_ `HappyStk`
	(HappyAbsSyn25  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Case happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_55 = happyReduce 4 15 happyReduction_55
happyReduction_55 ((HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn6  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Let happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_56 = happyReduce 6 15 happyReduction_56
happyReduction_56 ((HappyAbsSyn19  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Case happy_var_4 [Alt (getLoc happy_var_1) Nothing happy_var_2 happy_var_6]
	) `HappyStk` happyRest

happyReduce_57 = happyReduce 6 15 happyReduction_57
happyReduction_57 ((HappyAbsSyn19  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (If happy_var_2 happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_58 = happyReduce 4 15 happyReduction_58
happyReduction_58 (_ `HappyStk`
	(HappyAbsSyn19  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Fix happy_var_3
	) `HappyStk` happyRest

happyReduce_59 = happyReduce 6 15 happyReduction_59
happyReduction_59 (_ `HappyStk`
	(HappyAbsSyn19  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (FixN (unINT happy_var_3) happy_var_5
	) `HappyStk` happyRest

happyReduce_60 = happyReduce 10 15 happyReduction_60
happyReduction_60 ((HappyAbsSyn19  happy_var_10) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Fresh (unVARID happy_var_3) happy_var_5 happy_var_7 happy_var_10
	) `HappyStk` happyRest

happyReduce_61 = happySpecReduce_3  15 happyReduction_61
happyReduction_61 (HappyTerminal happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (Inst happy_var_1 (unVARID happy_var_3)
	)
happyReduction_61 _ _ _  = notHappyAtAll 

happyReduce_62 = happyReduce 5 15 happyReduction_62
happyReduction_62 (_ `HappyStk`
	(HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (TRACE (unVARID happy_var_2) happy_var_4
	) `HappyStk` happyRest

happyReduce_63 = happyReduce 5 15 happyReduction_63
happyReduction_63 ((HappyAbsSyn19  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn19
		 (Collect happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_64 = happySpecReduce_1  16 happyReduction_64
happyReduction_64 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn21
		 ([happy_var_1]
	)
happyReduction_64 _  = notHappyAtAll 

happyReduce_65 = happySpecReduce_2  16 happyReduction_65
happyReduction_65 (HappyAbsSyn21  happy_var_2)
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn21
		 (happy_var_1 : happy_var_2
	)
happyReduction_65 _ _  = notHappyAtAll 

happyReduce_66 = happySpecReduce_0  17 happyReduction_66
happyReduction_66  =  HappyAbsSyn21
		 ([]
	)

happyReduce_67 = happySpecReduce_1  17 happyReduction_67
happyReduction_67 (HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn21
		 (happy_var_1
	)
happyReduction_67 _  = notHappyAtAll 

happyReduce_68 = happySpecReduce_1  18 happyReduction_68
happyReduction_68 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn21
		 ([happy_var_1]
	)
happyReduction_68 _  = notHappyAtAll 

happyReduce_69 = happySpecReduce_1  18 happyReduction_69
happyReduction_69 (HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn21
		 (happy_var_1
	)
happyReduction_69 _  = notHappyAtAll 

happyReduce_70 = happySpecReduce_3  19 happyReduction_70
happyReduction_70 (HappyAbsSyn21  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn21
		 (happy_var_1 : happy_var_3
	)
happyReduction_70 _ _ _  = notHappyAtAll 

happyReduce_71 = happySpecReduce_1  20 happyReduction_71
happyReduction_71 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn25
		 ([happy_var_1]
	)
happyReduction_71 _  = notHappyAtAll 

happyReduce_72 = happySpecReduce_2  20 happyReduction_72
happyReduction_72 (HappyAbsSyn25  happy_var_2)
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn25
		 (happy_var_1 : happy_var_2
	)
happyReduction_72 _ _  = notHappyAtAll 

happyReduce_73 = happyReduce 4 21 happyReduction_73
happyReduction_73 ((HappyAbsSyn19  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn26
		 (Alt (getLoc happy_var_1) Nothing happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_74 = happyReduce 6 21 happyReduction_74
happyReduction_74 ((HappyAbsSyn19  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn26
		 (Alt (getLoc happy_var_1) (Just (Var $ unVARID happy_var_2)) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_75 = happyReduce 6 21 happyReduction_75
happyReduction_75 ((HappyAbsSyn19  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn26
		 (Alt (getLoc happy_var_1) (Just $ (Lit (LitInt (unINT happy_var_2)))) happy_var_4 happy_var_6
	) `HappyStk` happyRest

happyReduce_76 = happySpecReduce_1  22 happyReduction_76
happyReduction_76 (HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn27
		 (happy_var_1
	)
happyReduction_76 _  = notHappyAtAll 

happyReduce_77 = happySpecReduce_2  22 happyReduction_77
happyReduction_77 (HappyAbsSyn29  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn27
		 (PApp (unCONID happy_var_1) happy_var_2
	)
happyReduction_77 _ _  = notHappyAtAll 

happyReduce_78 = happySpecReduce_3  22 happyReduction_78
happyReduction_78 (HappyAbsSyn27  happy_var_3)
	_
	(HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn27
		 (PApp cons_con_name [happy_var_1, happy_var_3]
	)
happyReduction_78 _ _ _  = notHappyAtAll 

happyReduce_79 = happySpecReduce_1  23 happyReduction_79
happyReduction_79 _
	 =  HappyAbsSyn27
		 (PWild
	)

happyReduce_80 = happySpecReduce_1  23 happyReduction_80
happyReduction_80 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn27
		 (PVar $ unVARID happy_var_1
	)
happyReduction_80 _  = notHappyAtAll 

happyReduce_81 = happySpecReduce_1  23 happyReduction_81
happyReduction_81 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn27
		 (PApp (unCONID happy_var_1) []
	)
happyReduction_81 _  = notHappyAtAll 

happyReduce_82 = happySpecReduce_1  23 happyReduction_82
happyReduction_82 _
	 =  HappyAbsSyn27
		 (PApp "()" []
	)

happyReduce_83 = happySpecReduce_3  23 happyReduction_83
happyReduction_83 _
	(HappyAbsSyn27  happy_var_2)
	_
	 =  HappyAbsSyn27
		 (happy_var_2
	)
happyReduction_83 _ _ _  = notHappyAtAll 

happyReduce_84 = happySpecReduce_3  23 happyReduction_84
happyReduction_84 _
	(HappyAbsSyn29  happy_var_2)
	_
	 =  HappyAbsSyn27
		 (PApp (tuple_con_name (length happy_var_2)) happy_var_2
	)
happyReduction_84 _ _ _  = notHappyAtAll 

happyReduce_85 = happySpecReduce_2  23 happyReduction_85
happyReduction_85 _
	_
	 =  HappyAbsSyn27
		 (PApp nil_con_name []
	)

happyReduce_86 = happySpecReduce_3  23 happyReduction_86
happyReduction_86 _
	(HappyAbsSyn29  happy_var_2)
	_
	 =  HappyAbsSyn27
		 (plistify happy_var_2
	)
happyReduction_86 _ _ _  = notHappyAtAll 

happyReduce_87 = happySpecReduce_1  24 happyReduction_87
happyReduction_87 (HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn29
		 ([happy_var_1]
	)
happyReduction_87 _  = notHappyAtAll 

happyReduce_88 = happySpecReduce_2  24 happyReduction_88
happyReduction_88 (HappyAbsSyn29  happy_var_2)
	(HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn29
		 (happy_var_1 : happy_var_2
	)
happyReduction_88 _ _  = notHappyAtAll 

happyReduce_89 = happySpecReduce_1  25 happyReduction_89
happyReduction_89 (HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn29
		 ([happy_var_1]
	)
happyReduction_89 _  = notHappyAtAll 

happyReduce_90 = happySpecReduce_1  25 happyReduction_90
happyReduction_90 (HappyAbsSyn29  happy_var_1)
	 =  HappyAbsSyn29
		 (happy_var_1
	)
happyReduction_90 _  = notHappyAtAll 

happyReduce_91 = happySpecReduce_3  26 happyReduction_91
happyReduction_91 (HappyAbsSyn29  happy_var_3)
	_
	(HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn29
		 (happy_var_1 : happy_var_3
	)
happyReduction_91 _ _ _  = notHappyAtAll 

happyNewToken action sts stk
	= lexer(\tk -> 
	let cont i = happyDoAction i tk action sts stk in
	case tk of {
	L _ TEof -> happyDoAction 49 tk action sts stk;
	L _ TAssign -> cont 1;
	L _ (TInt _) -> cont 2;
	L _ (TVar _) -> cont 3;
	L _ (TCon _) -> cont 4;
	L _ TUnit -> cont 5;
	L _ TLParen -> cont 6;
	L _ TRParen -> cont 7;
	L _ TLBracket -> cont 8;
	L _ TRBracket -> cont 9;
	L _ TLCurBracket -> cont 10;
	L _ TRCurBracket -> cont 11;
	L _ TBang -> cont 12;
	L _ TCase -> cont 13;
	L _ TOf -> cont 14;
	L _ TEnd -> cont 15;
	L _ TLet -> cont 16;
	L _ TLetPrime -> cont 17;
	L _ TIn -> cont 18;
	L _ TIf -> cont 19;
	L _ TThen -> cont 20;
	L _ TElse -> cont 21;
	L _ TData -> cont 22;
	L _ TSig -> cont 23;
	L _ TFun -> cont 24;
	L _ TTRACE -> cont 25;
	L _ TFix -> cont 26;
	L _ TFresh -> cont 27;
	L _ TCollect -> cont 28;
	L _ TUnd -> cont 29;
	L _ TCons -> cont 30;
	L _ TColon -> cont 31;
	L _ TComma -> cont 32;
	L _ TNot -> cont 33;
	L _ TPlus -> cont 34;
	L _ TMinus -> cont 35;
	L _ TTimes -> cont 36;
	L _ TDiv -> cont 37;
	L _ TPercent -> cont 38;
	L _ TLAnd -> cont 39;
	L _ TLOr -> cont 40;
	L _ TEq -> cont 41;
	L _ TNe -> cont 42;
	L _ TLt -> cont 43;
	L _ TGt -> cont 44;
	L _ TLe -> cont 45;
	L _ TGe -> cont 46;
	L _ TArrow -> cont 47;
	L _ TBar -> cont 48;
	_ -> happyError' tk
	})

happyError_ 49 tk = happyError' tk
happyError_ _ tk = happyError' tk

happyThen :: () => P a -> (a -> P b) -> P b
happyThen = (>>=)
happyReturn :: () => a -> P a
happyReturn = (return)
happyThen1 = happyThen
happyReturn1 :: () => a -> P a
happyReturn1 = happyReturn
happyError' :: () => ((Located Token)) -> P a
happyError' tk = happyError tk

parser = happySomeParser where
  happySomeParser = happyThen (happyParse 0) (\x -> case x of {HappyAbsSyn5 z -> happyReturn z; _other -> notHappyAtAll })

typeParser = happySomeParser where
  happySomeParser = happyThen (happyParse 1) (\x -> case x of {HappyAbsSyn11 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


unINT :: Located Token -> Int
unINT t  = let (TInt i) = unLoc t in i 

unVARID :: Located Token -> VarId
unVARID t  = let (TVar i) = unLoc t in i

unCONID :: Located Token -> TyConId
unCONID t = let (TCon i) = unLoc t in i 

happyError :: (Located Token) -> P a
happyError (L loc tok) = throwError $ mkParseError "" loc (show tok)

mkConDecl :: OTcType -> P ConDecl
mkConDecl (TcCon c _n ts) = return $ ConDecl c ts
mkConDecl _ = error "Illegal data declaration"

fixConType :: [OTcType] -> OTcType 
fixConType (TcCon c 0 [] : ts') = TcCon c (length ts') ts'
fixConType [t] = t
fixConType t = error $ "Illegal type application : " ++ show t

appify :: Exp -> [Exp] -> Exp
appify e [] = e 
appify e (x:xs) = appify (App e x) xs

listify :: [Exp] -> Exp 
listify (e:es) = App (App (Con cons_con_name) e) (listify es)
listify [] = Con nil_con_name

plistify :: [Pat] -> Pat 
plistify [] = PApp nil_con_name []
plistify (x:xs) = PApp cons_con_name [x,plistify xs]

-- | TODO: Actually check declarations
checkRevDecls :: [Decl] -> P [Decl]
checkRevDecls = return 

extractTVar :: OTcType -> TyVarId 
extractTVar (TcVar x) = x
extractTVar _ = error "Not a variable"

checkDataHeader :: OTcType -> P (TyConId, [TyVarId])
checkDataHeader (TcCon c _ ts) = return (c, map extractTVar ts)
checkDataHeader _ = error "Illegal header declaration"

checkValDef :: SrcLoc -> VarId -> [VarId] -> Exp -> P Decl
checkValDef s i is e = return $ FunDecl s i is e
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 10 "<command-line>" #-}
# 1 "/usr/include/stdc-predef.h" 1 3 4

# 17 "/usr/include/stdc-predef.h" 3 4










































{-# LINE 10 "<command-line>" #-}
{-# LINE 1 "/usr/local/lib/ghc-7.10.1/include/ghcversion.h" #-}

















{-# LINE 10 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 13 "templates/GenericTemplate.hs" #-}

{-# LINE 46 "templates/GenericTemplate.hs" #-}


data Happy_IntList = HappyCons Int Happy_IntList





{-# LINE 67 "templates/GenericTemplate.hs" #-}

{-# LINE 77 "templates/GenericTemplate.hs" #-}



happyTrace string expr = Happy_System_IO_Unsafe.unsafePerformIO $ do
    Happy_System_IO.hPutStr Happy_System_IO.stderr string
    return expr




infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is (0), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (0) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action



happyDoAction i tk st
        = (happyTrace ("state: " ++ show (st) ++                        ",\ttoken: " ++ show (i) ++                       ",\taction: ")) $


          case action of
                (0)           -> (happyTrace ("fail.\n")) $
                                     happyFail i tk st
                (-1)          -> (happyTrace ("accept.\n")) $
                                     happyAccept i tk st
                n | (n < ((0) :: Int)) -> (happyTrace ("reduce (rule " ++ show rule                                                                ++ ")")) $

                                                   (happyReduceArr Happy_Data_Array.! rule) i tk st
                                                   where rule = ((negate ((n + ((1) :: Int)))))
                n                 -> (happyTrace ("shift, enter state "                                                  ++ show (new_state)                                                  ++ "\n")) $


                                     happyShift new_state i tk st
                                     where new_state = (n - ((1) :: Int))
   where off    = indexShortOffAddr happyActOffsets st
         off_i  = (off + i)
         check  = if (off_i >= ((0) :: Int))
                  then (indexShortOffAddr happyCheck off_i ==  i)
                  else False
         action
          | check     = indexShortOffAddr happyTable off_i
          | otherwise = indexShortOffAddr happyDefActions st

{-# LINE 147 "templates/GenericTemplate.hs" #-}
indexShortOffAddr arr off = arr Happy_Data_Array.! off








-----------------------------------------------------------------------------
-- HappyState data type (not arrays)

{-# LINE 170 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (0) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     happyDoAction i tk new_state (HappyCons (st) (sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state (HappyCons (st) (sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (0) tk st sts stk
     = happyFail (0) tk st sts stk
happySpecReduce_0 nt fn j tk st@((action)) sts stk
     = happyGoto nt j tk st (HappyCons (st) (sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (0) tk st sts stk
     = happyFail (0) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@((HappyCons (st@(action)) (_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (0) tk st sts stk
     = happyFail (0) tk st sts stk
happySpecReduce_2 nt fn j tk _ (HappyCons (_) (sts@((HappyCons (st@(action)) (_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (0) tk st sts stk
     = happyFail (0) tk st sts stk
happySpecReduce_3 nt fn j tk _ (HappyCons (_) ((HappyCons (_) (sts@((HappyCons (st@(action)) (_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (happyGoto nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (0) tk st sts stk
     = happyFail (0) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
         sts1@((HappyCons (st1@(action)) (_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (happyGoto nt j tk st1 sts1 r)

happyMonadReduce k nt fn (0) tk st sts stk
     = happyFail (0) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> happyGoto nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (0) tk st sts stk
     = happyFail (0) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k (HappyCons (st) (sts)) of
        sts1@((HappyCons (st1@(action)) (_))) ->
         let drop_stk = happyDropStk k stk

             off = indexShortOffAddr happyGotoOffsets st1
             off_i = (off + nt)
             new_state = indexShortOffAddr happyTable off_i



          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n (HappyCons (_) (t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction


happyGoto nt j tk st = 
   (happyTrace (", goto state " ++ show (new_state) ++ "\n")) $
   happyDoAction j tk new_state
   where off = indexShortOffAddr happyGotoOffsets st
         off_i = (off + nt)
         new_state = indexShortOffAddr happyTable off_i




-----------------------------------------------------------------------------
-- Error recovery ((0) is the error token)

-- parse error if we are in recovery and we fail again
happyFail (0) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (0) tk old_st (HappyCons ((action)) (sts)) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        happyDoAction (0) tk action sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (action) sts stk =
--      trace "entering error recovery" $
        happyDoAction (0) tk action sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.


{-# NOINLINE happyDoAction #-}
{-# NOINLINE happyTable #-}
{-# NOINLINE happyCheck #-}
{-# NOINLINE happyActOffsets #-}
{-# NOINLINE happyGotoOffsets #-}
{-# NOINLINE happyDefActions #-}

{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
