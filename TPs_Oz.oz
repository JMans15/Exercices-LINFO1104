declare B = Browse

% TP1: Somme des carrés
declare 
fun {SqSum2 N Acc} if N==1 then Acc+1 else {SqSum2 N-1 Acc+N*N} end end
fun {SqSum N} {SqSum2 N 0} end

% Test
{B {SqSum 10}}

% TP1: Mirroir
declare
fun {Mirror2 Num Acc}
   if Num == 0 then Acc else
      {Mirror2 Num div 10 Num mod 10 + 10*Acc}
   end
end
fun {Mirror Num} {Mirror2 Num 0} end

% Test
{B {Mirror 12345678901}}

% TP2: Ecriture listes
declare
L1 = a|nil
L2 = a|((b|(c|nil))|((d|nil)))
L3 = proc {$} {Browse oui} end|(proc {$} {Browse non} end|nil)
L4 = est|(une|(liste|nil))
L5 = (a|(p|nil))|nil
fun {Head L} case L of L1|L2 then L1 else invalid_input end end
fun {Tail L} case L of L1|L2 then L2 else invalid_input end end

% Test
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

% TP2: Length
declare
fun {LengthHelper List Length} if List == nil then Length else {LengthHelper List.2 Length+1} end end
fun {Length List} {LengthHelper List 0} end

% Test
{B {Length [r a p h]}}
{B {Length [[b o r] i s]}}
{B {Length [[l u i s]]}}

% TP2: Append
declare
fun {Append L1 L2} if L1 == nil then L2 else L1.1|{Append L1.2 L2} end end

% Test
{B {Append [a b] [c d]}}

% TP2: Take
declare
fun {Take L N} if N == 0 then nil else L.1|{Take L.2 N-1} end end

% Test
{B {Take [a b c 1 2 3 n s d a p 6 9] 5}}

% TP2: Drop
declare
fun {Drop L N} if N == 0 then L else {Drop L.2 N-1} end end

% Test
{B {Drop [a b c d e f g h i j k] 4}}

% TP2: FindString
declare
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

% Test
{B {FindString [1 2] [1 2 3 4 1 2 4 6 1 4 2 1 2]}}

% TP2: Btree
declare
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

% Test
Tree = btree(42 left: btree(26 left: btree(54 left: empty right: btree(18 left: empty right: empty))right: empty)right: btree(37 left: btree(11 left: empty right: empty)right: empty))
{B {Promenade Tree}}
{B {Sum1 Tree}}
{B {Sum2 Tree}}

% TP2: DictionaryFilter (infix left first)
declare
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

% Test
Dic = dict(key:10 info:person('Christian' 19) left:dict(key:7 info:person('Denys' 25) left:leaf right:dict(key:9 info:person('David' 7) left:leaf right:leaf)) right:dict(key:18 info:person('Rose' 12) left:dict(key:14 info:person('Ann' 27) left:leaf right:leaf) right:leaf))
{B {DictHelper Dic fun {$ I} I > 20 end nil}}

% TP2: Lists, Records et Tuples
declare fun {WhatsThis R}
	   if {IsList R} then list else
	      if {IsTuple R} then tuple else
		 record
	      end
	   end
	end
T1 = t1
T2 = t2
{B {WhatsThis '|'(a b)}} % Tuple de Label '|' et de 2 Fields à Features implicites
{B {WhatsThis '|'(a '|'(b nil))}} % Liste
{B {WhatsThis '|'(2:nil a)}} % Liste (Les Features sont simplement inversées ([a]))
{B {WhatsThis state(1 a 2)}} % Tuple de Label state et de 3 Fields à Features implicites
{B {WhatsThis state(1 3:2 2:a)}} % Tuple de label state et Fields désordonnés
{B {WhatsThis tree(v:a T1 T2)}} % Record de Lable tree et de Features v, 1 et 2
{B {WhatsThis a#b#c}} % Tuple
{B {WhatsThis [a b c]}} % Liste
{B {WhatsThis m|n|o}} % Tuple

% TP3: Pipeline
declare
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

% Test
{B {PipeLine 10}} % 1+9+25+49+81=165