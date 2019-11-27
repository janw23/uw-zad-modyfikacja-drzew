(* Autor:  Jan Wawszczak  *)
(* Review: Jakub Bedełek  *)


(* Porównuje przedziały [a, b] i [c, d]     	 *)
(* Najpierw porównuje początki przedziałów       *)
(* a jeśli są takie same to porównuje ich końce  *)
(* Zwraca -1 jeśli [a, b] < [c, d]          	 *)
(* Zwraca  0 jeśli  [a, b] = [c, d]         	 *)
(* Zwraca  1 jeśli  [a, b] = [c, d]         	 *)
let cmp (a, b) (c, d) =
    if a < c then -1
    else if a = c then (
        if b < d then -1
        else if b = d then 0
        else 1)
    else 1

(* Porównuje przedział [a, b] z liczbą [x] 			*)
(* Zwraca -1 jeśli [x] jest na lewo od przedziału	*)
(* 		   0 jeśli [x] należy do przedziału 		*)
(* 		   1 jeśli x jest na prawo od przedziału) 	*)
let cmp_with_num x (a, b) =
	if x < a then -1
	else if x > b then 1
	else 0

(* Dodaje do siebie liczby a, b. 							*)
(* Jeśli suma wychodzi poza zakres intów, to zwraca max_int *)
(* Założenie: obie liczby są nieujemne 						*)
let add_unsafe a b = if b = max_int || a + b < a then max_int else a + b

(* Zwraca true jeśli [a, b] a [c, d] nachodzą na siebie lub są przyległe *)
let joint (a, b) (c, d) =
	if (add_unsafe b 1 >= c && a <= add_unsafe d 1) ||
	   (add_unsafe d 1 >= a && c <= add_unsafe b 1) then 0
	else cmp (a, b) (c, d)

(* Zwracają odpowiednio minimum i maksimum z dwóch liczb całkowitych *)
let min (x : int) (y : int) = if x < y then x else y
and max (x : int) (y : int) = if x > y then x else y

(* Zwraca pierwszy lub drugi element z pary [a, b] *)
let first  (a, _) = a
and second (_, b) = b

(* Łączy dwa przyległe lub nachodzące przedziały w jeden *)
let unify (a, b) (c, d) = (min a c, max b d)

(* Sprawdza, czy da się ograniczyć przedział [a, b] przez [x] *)
let slicable_left  x (a, _) = x > a
and slicable_right x (_, b) = x < b

(* Ogranicza przedział [a, b] przez [x]. Wynik nie zawiera [x] *)
let slice_left  (x : int) (a, _) = (a, x - 1)
and slice_right (x : int) (_, b) = (x + 1, b)

(* ----------IMPLEMENTACJA DRZEW AVL---------- *)

(* Typ definiujący dwa rodzaje wierzchołków drzewa tworzącego Set *)
(* Warunek konieczny każdego przedziału [x, y]: x <= y            *)
type t =
    | Empty                              (* Pusty Set *)
    | Node of t * (int * int) * t * int * int  (* lewe poddrzewo, przedział, prawe poddrzewo, wysokość, liczba elem w poddrzewie *)

(* Zwraca wysokość drzewa [set] *)
let height set = match set with
  | Node (_, _, _, h, _) -> h
  | Empty -> 0

(* Oblicza liczbę całkowitych należących do przedziału [a, b] *)
(* Zwraca max_int jeśli jest ich więcej niż max_int 		  *)
let size (a, b) =
	if a > 0 then b - a + 1
	else (if a + max_int <= b then max_int
	else -(a - b) + 1)

(* Zwraca łączną liczbę liczb całkowitych należących do przedziałów w drzewie *)
let elem_count set =
	match set with
	| Empty -> 0
	| Node (_, _, _, _, c) -> c

(* Tworzy nowe drzewo z poddrzew l, r i korzenia o wartości k *)
let make l k r =
	Node (l, k, r, max (height l) (height r) + 1,
		 add_unsafe (add_unsafe (elem_count l) (elem_count r)) (size k))

(* Balansuje drzewo stworzone z poddrzew l, r i korzenia o wartości k 					   *)
(* Poddrzewa powinny być zbalansowane a różnica wysokości między nimi powinna nie być duża *)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else make l k r

(* Zwraca najmniejszy element w drzewie [set] *)
(* Zwraca wyjątek, jeśli [set] jest pusty     *)
let rec min_elt set = match set with
  | Node (Empty, k, _, _, _) -> k
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> raise Not_found

(* Usuwa najmniejszy element w drzewie [set] *)
(* Zwraca wyjątek, jeśli [set] jest pusty     *)
let rec remove_min_elt set = match set with
  | Node (Empty, _, r, _, _) -> r
  | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "PSet.remove_min_elt"

let empty = Empty
let is_empty set =
	set = Empty

(* Wstawia przedział [x] do drzewa [set] bez sprawdzania 			  *)
(* czy są jakieś przedziały, które są przyległe lub nachodzące na [x] *)
let rec add_brutal x set = match set with
  | Node (l, k, r, h, c) ->
  		let c = cmp x k in
      	if c = 0 then make l x r
      	else if c < 0 then
        	let nl = add_brutal x l in
        	bal nl k r
      	else
        	let nr = add_brutal x r in
        	bal l k nr
  | Empty -> make Empty x Empty

(* Łączy drzewa l, r używając v jako wartości nowego korzenia          *)
(* Wszystkie przedziały w l, v, r powinny być rozłączne i nieprzyległe *)
let rec join l v r =
  match (l, r) with
  | (Empty, _) -> add_brutal v r
  | (_, Empty) -> add_brutal v l
  | (Node(ll, lv, lr, lh, lc), Node(rl, rv, rr, rh, rc)) ->
      if lh > rh + 2 then bal ll lv (join lr v r) else
      if rh > lh + 2 then bal (join l v rl) rv rr else
      make l v r

(* Dostaje liczbę [x] oraz drzewo [set] 												   *)
(* Zwraca trójkę: (drzewo elementów < [x], czy [set] zawiera [x]?, drzewo elementów > [x]) *)
let split x set =
  let rec loop x = function
    | Empty -> (Empty, false, Empty)
    | Node (l, v, r, _, _) ->
        let c = cmp_with_num x v in
        if c = 0 then
        	let nl = if slicable_left  x v then add_brutal (slice_left  x v) l else l
        	and nr = if slicable_right x v then add_brutal (slice_right x v) r else r
        	in (nl, true, nr)
        else if c < 0 then let (ll, pres, rl) = loop x l in (ll, pres, join rl v r)
        else let (lr, pres, rr) = loop x r in (join l v lr, pres, rr)
  in let setl, pres, setr = loop x set in (setl, pres, setr)

(* Znajduje najbardziej prawy przedział należący do [set]    *)
(* który jest nachodzący lub przyległy do przedziału [x]     *)
let joint_rightmost x set =
	let rec helper acc = function
		| Node (l, k, r, _, _) ->
			if joint x k >= 0 then helper k r
			else helper acc l
		| Empty -> acc
	in helper x set

(* Znajduje najbardziej lewy przedział należący do [set]     *)
(* który jest nachodzący lub przyległy do przedziału [x]     *)
let joint_leftmost x set =
	let rec helper acc = function
		| Node (l, k, r, _, _) ->
			if joint x k <= 0 then helper k l
			else helper acc r
		| Empty -> acc
	in helper x set

(* Usuwa z set'a wszystkie elementy należące do przedziału [x, y] *)
let remove (x, y) set =
	let l = match split x set with (l,_,_) -> l
	and r = match split y set with (_,_,r) -> r
	in
		if is_empty r then l
	   	else join l (min_elt r) (remove_min_elt r)

(* Dodaje przedział [x] do [set] *)
let add x set =
	let rightmost = joint_rightmost x set
	and leftmost  = joint_leftmost  x set in
	let k = unify x (first leftmost, second rightmost)
	in add_brutal k (remove k set)

(* Zwraca true jeśli [x] należy do jakiegoś przedziału w [set] *)
let mem x set =
  	let rec loop = function
    	| Node (l, k, r, _, _) ->
        	let c = cmp_with_num x k in
        	c = 0 || loop (if c < 0 then l else r)
    	| Empty -> false
  	in loop set

let iter f set =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _, _) -> loop l; f k; loop r in
  loop set

let fold f set acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _, _) ->
          loop (f k (loop acc l)) r in
  loop acc set

(* Zwraca liczbę liczb całkowitych w [set], które są mniejsze lub równe [x] *)
let below x set =
	let s, pres = match split x set with (a, b, _) -> (a, b) in
	add_unsafe (elem_count s) (if pres then 1 else 0)
	
let elements set = 
  let rec loop acc = function
      Empty -> acc
    | Node(l, k, r, _, _) -> loop (k :: loop acc r) l in
  loop [] set;;

(* TESTY Z FORUM *)

let zle = ref 0
let test (id:int) (result:bool) (expected:bool) : unit =
    if result <> expected then begin
        Printf.printf "Zly wynik testu %d!\n" id;
        incr zle
    end;;

let s = empty;;
test 11 (is_empty s) true;;
test 12 (is_empty (add (1, 1) s)) false;;

let s = add (10, 12) empty;;
test 21 (mem 9 s) false;;
test 22 (mem 10 s) true;;
test 23 (mem 12 s) true;;
test 24 (mem 13 s) false;;

let s = add (4, 7) s;;
test 25 (mem 8 s) false;;
test 26 (mem 11 s) true;;
test 27 (mem 5 s) true;;
test 28 (mem 3 s) false;;


let s = add (1, 1) (add (15, 16) (add (10, 14) (add (6, 9) empty)));;
test 31 (mem 10 (remove (10, 10) s)) false;;
test 32 (is_empty (remove (1, 20) s)) true;;
test 33 (mem 7 (remove (8, 15) s)) true;;

let s = add (-1, 1) (add (3, 7) (add (10, 12) (add (15, 18)
        (add (-15, -13) empty))));;
let s = remove (-10, 12) s;;
test 34 (is_empty s) false;;
test 35 (mem 5 s) false;;
test 36 (mem (-10) s) false;;
test 37 (mem (-15) s) true;;
test 38 (mem 17 s) true;;


test 41 (elements (add (4, 5) (add (7, 8) empty)) = [(4, 5); (7, 8)]) true;;
test 42 (elements (add (1, 1) (add (11, 14) (add (6, 9) (add (4, 5) empty))))
        = [(1, 1); (4, 9); (11, 14)]) true;;


let s = add (3, 4) (add (8, 10) (add (15, 20) empty));;
test 51 (below 2 s = 0) true;;
test 52 (below 3 s = 1) true;;
test 53 (below 10 s = 5) true;;
test 54 (below 15 s = 6) true;;
test 55 (below 100 s = 11) true;;
let s = add (1, max_int) (add (-1, 0) empty);;
test 56 (below max_int s = max_int) true;;
let s = add (-min_int, max_int) empty;;
test 57 (below max_int s = max_int) true;;
test 58 (below min_int s = 1) true;;


let s = add (3, 4) (add (8, 10) (add (15, 20) empty));;
let l, pres, r = split 9 s;;
test 61 (mem 9 l) false;;
test 62 (mem 9 r) false;;
test 63 (mem 8 l) true;;
test 64 (mem 10 r) true;;
test 65 pres true;;
test 66 (mem 7 l) false;;
test 67 (mem 4 l) true;;
test 68 (mem 11 r) false;;
test 69 (mem 16 r) true;;


let s = add (1, 1) (add (11, 14) (add (6, 9) (add (4, 5) empty)));;
let a = ref [];;
let foo x = a := x::!a; ();;
test 71 (iter foo s; !a = [(11, 14); (4, 9); (1, 1)]) true;;


let s = add (1, 1) (add (11, 14) (add (6, 9) (add (4, 5) empty)));;
let foo x a = x::a;;
test 81 (fold foo s [] = [(11, 14); (4, 9); (1, 1)]) true;;

let _ =
    if !zle = 0 then ()
    else Printf.printf "\nZlych odpowiedzi: %d.\n" !zle
;;