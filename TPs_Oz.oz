declare B = Browse

% TP1: Somme des carres
local
   fun {SqSum N} fun {SqSum2 N Acc} if N==1 then Acc+1 else {SqSum2 N-1 Acc+N*N} end end in {SqSum2 N 0} end
in
% Test
   {B somme_carres__}
   {B {SqSum 10}}
   {B {SqSum 2}}
   {B {SqSum 3}}
end

% TP1: Mirroir
local
   fun {Mirror2 Num Acc}
      if Num == 0 then Acc else
	 {Mirror2 Num div 10 Num mod 10 + 10*Acc}
      end
   end
   fun {Mirror Num} {Mirror2 Num 0} end
in
% Test
   {B mirror__}
   {B {Mirror 12345678901}}
end
% TP2: Ecriture listes
local
   L1 = a|nil
   L2 = a|((b|(c|nil))|((d|nil)))
   L3 = proc {$} {Browse oui} end|(proc {$} {Browse non} end|nil)
   L4 = est|(une|(liste|nil))
   L5 = (a|(p|nil))|nil
   fun {Head L} case L of L1|L2 then L1 else invalid_input end end
   fun {Tail L} case L of L1|L2 then L2 else invalid_input end end
in
% Test
   {B ecriture_listes__}
   {B L1}
   {B L2}
   {B L3}
   {B L4}
   {B L5}
   {B ceci|L4}
   {L3.1}
   {B L2.2}
   {B {Head [a b c]}}
   {B {Tail [a b c]}}
end
% TP2: Length
local
   fun {LengthHelper List Length} if List == nil then Length else {LengthHelper List.2 Length+1} end end
   fun {Length List} {LengthHelper List 0} end
in
% Test
   {B length__}
   {B {Length [r a p h]}}
   {B {Length [[b o r] i s]}}
   {B {Length [[l u i s]]}}
end
% TP2: Append
local
   fun {Append L1 L2} if L1 == nil then L2 else L1.1|{Append L1.2 L2} end end
in
% Test
   {B append__}
   {B {Append [a b d e f] [c d e f]}}
end
% TP2: Take
local
   fun {Take L N} if N == 0 then nil else L.1|{Take L.2 N-1} end end
in
% Test
   {B take__}
   {B {Take [a b c 1 2 3 n s d a p 6 9] 5}}
end
% TP2: Drop
local
   fun {Drop L N} if N == 0 then L else {Drop L.2 N-1} end end
in
% Test
   {B drop__}
   {B {Drop [a b c d e f g h i j k] 4}}
end
% TP2: FindString
local
   fun {Prefix S L} case S of S1|S2 then if S1 \= L.1 then false else if S2 == nil then true else {Prefix S2 L.2} end end else false end end 
   fun {FindStringHelper S L A N}
      case L of _|L2 then
	 if {Prefix S L} then
	    N|{FindStringHelper S L2 A N+1}
	 else {FindStringHelper S L2 A N+1} end
      [] nil then A
      else error end
   end
   fun {FindString S L}
      {FindStringHelper S L nil 0}
   end
in
% Test
   {B findString__}
   {B {FindString [1 2] [1 2 3 4 1 2 4 6 1 4 2 1 2]}}
end
% TP2: Btree
local
   fun {PromenadeHelper BT Acc}
      case BT of btree(A left: L right: R) then
	 if L == empty then
	    if R == empty then
	       A|Acc
	    else
	       A|{PromenadeHelper R Acc}
	    end
	 else if R == empty then
		 A|{PromenadeHelper L Acc}
	      else 
		 A|{PromenadeHelper L {PromenadeHelper R Acc}}
	      end
	 end
      end
   end
   fun {Promenade BT} {PromenadeHelper BT nil} end
   fun {Sum1 BT} {FoldL {Promenade BT} fun {$ X Y} X+Y end 0} end
   fun {Sum2Helper BT Acc}
      case BT of btree(A left: L right: R) then
	 if L == empty then
	    if R == empty then
	       A
	    else
	       A+{Sum2Helper R Acc}
	    end
	 else if R == empty then
		 A+{Sum2Helper L Acc}
	      else 
		 A+{Sum2Helper L Acc}+{Sum2Helper R Acc}
	      end
	 end
      end
   end
   fun {Sum2 BT}{Sum2Helper BT 0}end
   Tree
in
% Test
   {B btree__}
   Tree = btree(42 left: btree(26 left: btree(54 left: empty right: btree(18 left: empty right: empty))right: empty)right: btree(37 left: btree(11 left: empty right: empty)right: empty))
   {B {Promenade Tree}}
   {B {Sum1 Tree}}
   {B {Sum2 Tree}}
end
% TP2: DictionaryFilter (infix left first)
local
   fun {DictHelper Dict F Ls}
      case Dict of dict(key: K info: I left: L right: R) then
	 if L == leaf then
	    if R == leaf then
	       if {F I.2} then K#I|Ls else Ls end
	    else
	       if {F I.2} then K#I|{DictHelper R F Ls}
	       else {DictHelper R F Ls} end
	    end
	 else if R == leaf then
		 if {F I.2} then K#I|{DictHelper L F Ls}
		 else {DictHelper L F Ls} end
	      else
		 if {F I.2} then K#I|{DictHelper L F {DictHelper R F Ls}}
		 else {DictHelper L F {DictHelper R F Ls}} end
	      end
	 end
      else wrong_input
      end
   end
   Dic
in
% Test
   {B dictionaryFilter__}
   Dic = dict(key:10 info:person('Christian' 19) left:dict(key:7 info:person('Denys' 25) left:leaf right:dict(key:9 info:person('David' 7) left:leaf right:leaf)) right:dict(key:18 info:person('Rose' 12) left:dict(key:14 info:person('Ann' 27) left:leaf right:leaf) right:leaf))
   {B {DictHelper Dic fun {$ I} I > 20 end nil}}
end

% TP2: Lists, Records et Tuples
local
   fun {WhatsThis R}
      if {IsList R} then list else
	 if {IsTuple R} then tuple else
	    record
	 end
      end
   end
   T1=t1
   T2=t2
in
   {B lists_records_tuples__}
% Tuple de Label | et de 2 Fields à Features implicites
% Liste
% Liste (Les Features sont simplement inversees ([a]))
% Tuple de Label state et de 3 Fields à Features implicites
% Tuple de label state et Fields désordonnes
% Record de Lable tree et de Features v 1 et 2
% Tuple
% Liste
% Tuple
   {B {WhatsThis '|'(a b)}} 
   {B {WhatsThis '|'(a '|'(b nil))}} 
   {B {WhatsThis '|'(2:nil a)}} 
   {B {WhatsThis state(1 a 2)}} 
   {B {WhatsThis state(1 3:2 2:a)}} 
   {B {WhatsThis tree(v:a T1 T2)}}
   {B {WhatsThis a#b#c}} 
   {B {WhatsThis [a b c]}} 
   {B {WhatsThis m|n|o}}
end

% TP3: Pipeline
local
   fun {GenerateList N}
      local fun {Helper N Acc} if N == 0 then 0|Acc else {Helper N-1 N|Acc} end end
      in {Helper N nil} end
   end
   fun {MyFilter L F}
      local fun {Helper L F Acc} case L of L1|L2 then if {F L1} then L1|{Helper L2 F Acc} else {Helper L2 F Acc} end else Acc end end
      in {Helper L F nil} end
   end
   fun {MyMap L F}
      local fun {Helper L F Acc} case L of L1|L2 then {F L1}|{Helper L2 F Acc} else Acc end end
      in {Helper L F nil} end
   end
   fun {MyFoldL L F P}
      case L of L1|L2 then if L2 == nil then {F L1 P} else {F L1 {MyFoldL L2 F P}} end else error end
   end
   fun {PipeLine N}
      P1 P2 P3 in
      P1 = {GenerateList N}
      P2 = {MyFilter P1 fun {$ X} X mod 2 \= 0 end}
      P3 = {MyMap P2 fun {$ X} X * X end}
      {MyFoldL P3 fun {$ Acc X} X + Acc end 0}
   end
in
% Test
   {B pipeline__}
   {Browse {PipeLine 100}} % 1+9+25+49+81=165
end

% TP8: Counter
local
   fun {AddToDict Elem Dict Done}
      case Dict of D1|D2 then
	 case D1 of K#V then
	    if K == Elem then
	       K#(V+1)|{AddToDict Elem D2 true}
	    else
	       K#V|{AddToDict Elem D2 Done}
	    end
	 end
      [] nil then if Done then nil else Elem#1|nil end
      else error end
   end
   fun {Counter InS}
      fun {Helper InS Last} New in
	 thread
	    case InS of F|N then
	       New = {AddToDict F Last false}
	       New|{Helper N New}
	    end
	 end
      end
   in
      {Helper InS nil}
   end
in
% Test
   {B counter__}
   local InS in
      {Browse {Counter InS}}
      InS = a|b|a|a|d|c|b|_
   end
end

% TP8: Gates
local
   fun {NotGate S}
      thread
	 case S of S1|S2 then
	    (S1+1) mod 2|{NotGate S2}
	 end
      end
   end
   fun {AndGate X Y}
      thread
	 case X of X1|X2 then
	    case Y of Y1|Y2 then
	       if X1==Y1 andthen X1 == 1 then 1|{AndGate X2 Y2}
	       else 0|{AndGate X2 Y2}
	       end
	    end
	 end
      end
   end
   fun {OrGate X Y}
      thread
	 case X of X1|X2 then
	    case Y of Y1|Y2 then
	       if X1==1 orelse Y1==1 then 1|{OrGate X2 Y2}
	       else 0|{OrGate X2 Y2}
	       end
	    end
	 end
      end
   end
   fun {Simulate G Ss}
      thread
	 case {Label G} of gate then
	    case G.value of 'or' then {OrGate {Simulate G.1 Ss} {Simulate G.2 Ss}}
	    [] 'and' then {AndGate {Simulate G.1 Ss} {Simulate G.2 Ss}}
	    [] 'not' then {NotGate {Simulate G.1 Ss}}
	    end
	 [] input then Ss.(G.1)
	 else error end
      end
   end
   G = gate(value:'or' gate(value:'and' input(x) input(y)) gate(value:'not' input(z)))
in
   local Ss in
      {B simulate__}
      {Browse {Simulate G Ss}}
      Ss = input(x: 1|0|1|0|_ y:0|1|0|1|_ z:1|1|0|0|_)
   end
end
