let print s   = print_string s
and println s = print_string (s ^ "\n");;

let str_pair (a, b) =
	"(" ^ (string_of_int a) ^ ", " ^ (string_of_int b) ^ ")"


(* Porównuje przedziały [a, b] i [c, d]     *)
(* Najpierw porównuje początki przedziałów       *)
(* a jeśli są takie same to porównuje ich końce  *)
(* Zwraca -1 jeśli [a, b] < [c, d]          *)
(* Zwraca  0 jeśli  [a, b] = [c, d]         *)
(* Zwraca  1 jeśli  [a, b] = [c, d]         *)
let cmp (a, b) (c, d) =
    if a < c then -1
    else if a = c then (
        if b < d then -1
        else if b = d then 0
        else 1)
    else 1
    (* TODO: sprawdzić, czy nie wystarczy jedynie porównywać pierwszych elementów *)

(* Porównuje przedział [a, b] z liczbą [x] 			*)
(* Zwraca -1 jeśli [x] jest na lewo od przedziału	*)
(* 		   0 jeśli [x] należy do przedziału 		*)
(* 		   1 jeśli x jest na prawo od przedziału) 	*)
let cmp_with_num x (a, b) =
	if x < a then -1
	else if x > b then 1
	else 0

let add_unsafe a b = if b = max_int || a + b < a then max_int else a + b

(* Zwraca true jeśli [a, b] a [c, d] nachodzą na siebie lub są przyległe *)
let joint (a, b) (c, d) =
    (*if (b + 1 >= c && a <= d + 1) || (d + 1 >= a && c <= b + 1) then 0
	else cmp (a, b) (c, d) *)
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
let unify (a, b) (c, d) =
    (min a c, max b d)

let slicable_left  x (a, _) = x > a
and slicable_right x (_, b) = x < b

let slice_left  (x : int) (a, _) = (a, x - 1)
and slice_right (x : int) (_, b) = (x + 1, b)

(* ----------IMPLEMENTACJA DRZEW AVL---------- *)

(* Typ definiujący dwa rodzaje wierzchołków drzewa tworzącego Set *)
(* Warunek konieczny każdego przedziału [x, y]: x <= y            *)
type t =
    | Empty                              (* Pusty Set *)
    | Node of t * (int * int) * t * int  (* lewe poddrzewo, przedział, prawe poddrzewo, wysokość *)

let height set = match set with
  | Node (_, _, _, h) -> h
  | Empty -> 0

let make l k r = Node (l, k, r, max (height l) (height r) + 1)

(* DEBUG FUNCTION TO USE IN ASSERTIONS *)
(* CHECKS IF SET'S TREE IS BALANCED    *)
let is_balanced set =
	let rec helper s =
		match s with
		| Empty -> (0, true)
		| Node (l, _, r, _) ->
			let l_first, l_second = helper l
			and r_first, r_second = helper r
			in let (a, b) = (max l_first r_first + 1, l_second && r_second && (abs (l_first - r_first) <= 2))
			in (*print_string ("(" ^ (string_of_int a) ^ ", " ^ (if b then "true" else "false") ^ ")");
			   print_string ("(" ^ (string_of_int l_first) ^ ", ");
			   print_string ((if l_second then "true" else "false") ^ ", ");
			   print_string ((if r_second then "true" else "false") ^ ", ");
			   print_string ((string_of_int r_first) ^ ")\n");*)
			   (a, b)
	in match helper set with (_, res) -> res

(* Zwraca set stworzony z drzew l, r i elementu o wartości k między nimi 			*)
(* Dodatkowo drugim elementem zwracanej pary jest true, jeśli coś zostało zmienione *)
(* albo false, jeśli drzewo jest już zbalansowane i nic nie zmieniono 				*)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, r, max hl hr + 1)

let rec min_elt set = match set with
  | Node (Empty, k, _, _) -> k
  | Node (l, _, _, _) -> min_elt l
  | Empty -> raise Not_found

let rec remove_min_elt set = match set with
  | Node (Empty, _, r, _) -> r
  | Node (l, k, r, _) -> assert(is_balanced (bal (remove_min_elt l) k r)); bal (remove_min_elt l) k r
  | Empty -> invalid_arg "PSet.remove_min_elt"

let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

let empty = Empty

let is_empty set = 
  set = Empty

(* Wstawia przedział [x] do drzewa [set] bez sprawdzania 			  *)
(* czy są jakieś przedziały, które są przyległe lub nachodzące na [x] *)
(* TODO *)
(* T = O(log(height set)) *)
let rec add_brutal x set = match set with
  | Node (l, k, r, h) ->
      let c = cmp x k in
      if c = 0 then Node (l, x, r, h)
      else if c < 0 then
        let nl = add_brutal x l in
        bal nl k r
      else
        let nr = add_brutal x r in
        bal l k nr
  | Empty -> Node (Empty, x, Empty, 1)

(* Łączy drzewa l, r używając v jako wartości nowego korzenia          *)
(* Wszystkie przedziały w l, v, r powinny być rozłączne i nieprzyległe *)
(* T = O(height l - height r)                                           *)
let rec join l v r =
  match (l, r) with
  | (Empty, _) -> add_brutal v r
  | (_, Empty) -> add_brutal v l
  | (Node(ll, lv, lr, lh), Node(rl, rv, rr, rh)) ->
      if lh > rh + 2 then bal ll lv (join lr v r) else
      if rh > lh + 2 then bal (join l v rl) rv rr else
      make l v r

(* Dostaje liczbę [x] oraz drzewo [set] 												   *)
(* Zwraca trójkę: (drzewo elementów < [x], czy [set] zawiera [x]?, drzewo elementów > [x]) *)
(* TODO: Raczej działa xD *)
let split x set =
  let rec loop x = function
    | Empty -> (Empty, false, Empty)
    | Node (l, v, r, _) ->
        let c = cmp_with_num x v in
        if c = 0 then
        	let nl = if slicable_left  x v then add_brutal (slice_left  x v) l else l
        	and nr = if slicable_right x v then add_brutal (slice_right x v) r else r
        	in (nl, true, nr)
        else if c < 0 then
         	let (ll, pres, rl) = loop x l in (ll, pres, join rl v r)
        else
          	let (lr, pres, rr) = loop x r in (join l v lr, pres, rr)
  in
	let setl, pres, setr = loop x set in
	  	assert(is_balanced setl);
	  	assert(is_balanced setr);
	  	(setl, pres, setr)

(* Znajduje najbardziej prawy przedział należący do [set]    *)
(* który jest nachodzący lub przyległy do przedziału [x]     *)
let joint_rightmost x set =
	let rec helper acc = function
		| Node (l, k, r, _) ->
			if joint x k >= 0 then helper k r
			else helper acc l
		| Empty -> acc
	in helper x set

(* Znajduje najbardziej lewy przedział należący do [set]     *)
(* który jest nachodzący lub przyległy do przedziału [x]     *)
let joint_leftmost x set =
	let rec helper acc = function
		| Node (l, k, r, _) ->
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

let add x set =
	let rightmost = joint_rightmost x set
	and leftmost  = joint_leftmost  x set in
	(*println ("rightmost = " ^ (str_pair rightmost));
	println ("leftmost = " ^ (str_pair leftmost));*)
	let k = unify x (first leftmost, second rightmost)
	in add_brutal k (remove k set)

(* Zwraca true jeśli [x] należy do jakiegoś przedziału w [set] *)
let mem x set =
  	let rec loop = function
    	| Node (l, k, r, _) ->
        	let c = cmp_with_num x k in
        	c = 0 || loop (if c < 0 then l else r)
    	| Empty -> false
  	in loop set

let exists = mem

let iter f set =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _) -> loop l; f k; loop r in
  loop set

let fold f set acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _) ->
          loop (f k (loop acc l)) r in
  loop acc set

let size (a, b) = b - a + 1

(*TODO *)
let below x set =
	let s = (match (split (x + 1) set) with (l, _, _) -> l) in
	let f a acc = add_unsafe acc (size a) in
	fold f s 0


let elements set = 
  let rec loop acc = function
      Empty -> acc
    | Node(l, k, r, _) -> loop (k :: loop acc r) l in
  loop [] set;;

(* -------DEBUGGING------- *)

let set_from_list l =
	let rec helper set lst =
		match lst with
		| [] -> set
		| h :: t -> helper (add_brutal h set) t
	in helper empty l

let r_stride x r m =
	x + (Random.int r) + m

let gen_interval_list n =
	let rec helper k p acc =
		if k = 0 then acc
		else 
			let l = r_stride p 20 1 in
			let r = r_stride l 20 0 in
			helper (k - 1) (r_stride r 20 0) ((l, r) :: acc)
	in List.rev (helper n (-100) [])

let split_list x l =
	let rec helper acc lst =
		match lst with
		| [] -> (acc, false, lst)
		| h :: t ->
			let c = cmp_with_num x h in
			if c = 0 then ((if slicable_left  x h then (slice_left  x h) :: acc else acc),
						   true,
						   (if slicable_right x h then (slice_right x h) :: t   else t))
			else if c < 0 then (acc, false, lst)
			else helper (h :: acc) t
	in match helper [] l with
		(l, pres, r) -> (List.rev l, pres, r)

let rec dfs f set =
	match set with
	| Node(l, k, r, h) -> f (l, k, r, h); dfs f l; dfs f r
	| Empty -> ()

let str_list l =
	let rec helper lst =
		match lst with
		| [] -> "]"
		| h :: [] -> (str_pair h) ^ (helper [])
		| h :: t  -> (str_pair h) ^ "; " ^ (helper t)
	in "[" ^ (helper l)



(*

let ilst = gen_interval_list 10000;;
println (str_list ilst);;

let iset = set_from_list ilst;;
iter (function e -> println (str_pair e)) iset;;
assert(is_balanced iset);;

let ilst_l, ilst_pres, ilst_r = split_list 28 ilst;;
let iset_l, iset_pres, iset_r = split 28 iset;;

println "List split result:";;
println ("Left = " ^ (str_list ilst_l));;
println ("Pres = " ^ (if ilst_pres then "true" else "false"));;
println ("Right = " ^ (str_list ilst_r));;

println "Set split result:";;
println ("Left = " ^ (str_list (elements iset_l)));;
println ("Pres = " ^ (if iset_pres then "true" else "false"));;
println ("Right = " ^ (str_list (elements iset_r)));;
println "\n\n\n";;

assert(ilst_pres = iset_pres);;
assert(ilst_l = elements iset_l);;
assert(ilst_r = elements iset_r);;

println "removing test";;
let iset = set_from_list ilst;;

println "dfs";;
dfs (function (l, k, r, h) -> println (str_pair k ^ " : " ^ (string_of_int h))) iset;;

println (str_list (elements iset));;
println (str_list (elements (remove (1000, 6000) iset)));;
*)


(* TESTOWANKO *)

let string_of_tree t = 
  let rec fmt_tree fmt = function Empty -> Format.fprintf fmt "Empty"
    | Node (l,(a,b),r,_) ->
        Format.fprintf fmt "@[<hv 5>Node(%a,@ (%d,%d),@ %a@,)@]"
          fmt_tree l a b fmt_tree r
  in
  fmt_tree Format.str_formatter t;
  Format.flush_str_formatter ();;

let print_tree t =
  print_string (string_of_tree t);;


let zle = ref 0
let test n b =
	print_string (string_of_int n ^ "\n");
	flush_all ();
  if not b then begin
    Printf.printf "Zly wynik testu %d!!\n" n;
    incr zle
  end

(* pierwsze testy *)
let s=empty;;
let s = add (3,7) s;;
test 23 (elements s = [(3, 7)]);;
let s = add (3,7) s;;
test 25 (elements s = [(3, 7)]);;
let s = add (7,9) s;;
test 27 (elements s = [(3, 9)]);;
let s = add (10,13) s;;
test 29 (elements s = [(3, 13)]);;
let s = add (1,2) s;;  
test 31 (elements s = [(1, 13)]);;
let s = add (15,28) s;;
test 33 (elements s = [(1, 13); (15, 28)]);;
let s = add (14,14) s;;
test 35 (elements s = [(1, 28)]);;
test 36 (below 17 s = 17);;
test 37 (below 17 s = 17);;
test 38 (below 50 s = 28);;


(* testy konkretne *)


let s = empty;;
test 45 (is_empty s);;
let s = add (-1,1) s;;
test 47 (not (is_empty s));;
let s = add (3,4) s;;
let s = add (6,7) s;;
let s = add (9,10) s;;
test 51 (not (is_empty s));;
let s = add (14,15) s;;
let s = add (17,18) s;;
let s = add (20,21) s;;
test 55 (not (is_empty s));;
test 56 (elements s = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 57 (fold (fun _ i -> i+1) s 0 = 7);;


(* add *)
test 61 (elements (add (-10,-5) s) = [(-10, -5); (-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 62 (elements (add (-10,-2) s) = [(-10, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 63 (elements (add (-10,-1) s) = [(-10, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 64 (elements (add (-10,0) s) = [(-10, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 65 (elements (add (-10,1) s) = [(-10, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 66 (elements (add (-10,2) s) = [(-10, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 67 (elements (add (-10,8) s) = [(-10, 10); (14, 15); (17, 18); (20, 21)]);;
test 68 (elements (add (-10,12) s) = [(-10, 12); (14, 15); (17, 18); (20, 21)]);;
test 69 (elements (add (-10,17) s) = [(-10, 18); (20, 21)]);;
test 70 (elements (add (-10,19) s) = [(-10, 21)]);;
test 71 (elements (add (-10,21) s) = [(-10, 21)]);;
test 72 (elements (add (-10,25) s) = [(-10, 25)]);;
test 73 (elements (add (-1,25) s) = [(-1, 25)]);;
test 74 (elements (add (0,25) s) = [(-1, 25)]);;
test 75 (elements (add (1,25) s) = [(-1, 25)]);;
test 76 (elements (add (2,25) s) = [(-1, 25)]);;
test 77 (elements (add (3,25) s) = [(-1, 1); (3, 25)]);;
test 78 (elements (add (11,25) s) = [(-1, 1); (3, 4); (6, 7); (9, 25)]);;
test 79 (elements (add (12,25) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (12, 25)]);;
test 80 (elements (add (15,25) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 25)]);;
test 81 (elements (add (19,25) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 25)]);;
test 82 (elements (add (20,25) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 25)]);;
test 83 (elements (add (21,25) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 25)]);;
test 84 (elements (add (22,25) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 25)]);;
test 85 (elements (add (23,25) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21); (23, 25)]);;
test 86 (elements (add (25,25) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21); (25, 25)]);;
test 87 (elements (add (2,12) s) = [(-1, 12); (14, 15); (17, 18); (20, 21)]);;
test 88 (elements (add (3,12) s) = [(-1, 1); (3, 12); (14, 15); (17, 18); (20, 21)]);;
test 89 (elements (add (4,12) s) = [(-1, 1); (3, 12); (14, 15); (17, 18); (20, 21)]);;
test 90 (elements (add (5,12) s) = [(-1, 1); (3, 12); (14, 15); (17, 18); (20, 21)]);;
test 91 (elements (add (6,12) s) = [(-1, 1); (3, 4); (6, 12); (14, 15); (17, 18); (20, 21)]);;
test 92 (elements (add (6,13) s) = [(-1, 1); (3, 4); (6, 15); (17, 18); (20, 21)]);;
test 93 (elements (add (5,13) s) = [(-1, 1); (3, 15); (17, 18); (20, 21)]);;

(* remove *)
test 97 (elements (remove (-10,-2) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 98 (elements (remove (-10,-1) s) = [(0, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 99 (elements (remove (-10,0) s) = [(1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 100 (elements (remove (-10,1) s) = [(3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 101 (elements (remove (-10,2) s) = [(3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 102 (elements (remove (-10,9) s) = [(10, 10); (14, 15); (17, 18); (20, 21)]);;
test 103 (elements (remove (-10,20) s) = [(21, 21)]);;
test 104 (elements (remove (-10,21) s) = []);;
test 105 (elements (remove (-10,28) s) = []);;
test 106 (elements (remove (-2,28) s) = []);;
test 107 (elements (remove (-1,28) s) = []);;
test 108 (elements (remove (0,28) s) = [(-1, -1)]);;
test 109 (elements (remove (1,28) s) = [(-1, 0)]);;
test 110 (elements (remove (2,28) s) = [(-1, 1)]);;
test 111 (elements (remove (3,28) s) = [(-1, 1)]);;
test 112 (elements (remove (4,28) s) = [(-1, 1); (3, 3)]);;
test 113 (elements (remove (5,28) s) = [(-1, 1); (3, 4)]);;
test 114 (elements (remove (6,28) s) = [(-1, 1); (3, 4)]);;
test 115 (elements (remove (10,28) s) = [(-1, 1); (3, 4); (6, 7); (9, 9)]);;
test 116 (elements (remove (20,28) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18)]);;
test 117 (elements (remove (21,28) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 20)]);;
test 118 (elements (remove (25,28) s) = [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 119 (elements (remove (1,5) s) = [(-1, 0); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 120 (elements (remove (1,6) s) = [(-1, 0); (7, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 121 (elements (remove (1,7) s) = [(-1, 0); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 122 (elements (remove (2,5) s) = [(-1, 1); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 123 (elements (remove (3,5) s) = [(-1, 1); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 124 (elements (remove (3,6) s) = [(-1, 1); (7, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 125 (elements (remove (3,7) s) = [(-1, 1); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 126 (elements (remove (2,6) s) = [(-1, 1); (7, 7); (9, 10); (14, 15); (17, 18); (20, 21)]);;
test 127 (elements (remove (2,7) s) = [(-1, 1); (9, 10); (14, 15); (17, 18); (20, 21)]);;


(* mem *)
test 131 (mem (-10) s = false);;
test 132 (mem (-2) s = false);;
test 133 (mem (-1) s = true);;
test 134 (mem 0 s = true);;
test 135 (mem 1 s = true);;
test 136 (mem 2 s = false);;
test 137 (mem 10 s = true);;
test 138 (mem 11 s = false);;
test 139 (mem 13 s = false);;
test 140 (mem 14 s = true);;
test 141 (mem 21 s = true);;
test 142 (mem 22 s = false);;


(* iter *)
test 146 (let l = ref [] in iter (fun x -> l:=x::!l) s; List.rev !l = elements s);;
test 147 (let t = ref true in iter (fun _ -> t:=false) empty; !t);;


(* fold *)
test 151 (fold (fun x l -> x::l) s [] = List.rev (elements s));;
test 152 (fold (fun _ _ -> false) empty true);;


(* below *)
test 156 (below (-10) s = 0);;
test 157 (below (-1) s = 1);;
test 158 (below 0 s = 2);;
test 159 (below 1 s = 3);;
test 160 (below 2 s = 3);;
test 161 (below 6 s = 6);;
test 162 (below 7 s = 7);;
test 163 (below 8 s = 7);;
test 164 (below 9 s = 8);;
test 165 (below 20 s = 14);;
test 166 (below 21 s = 15);;
test 167 (below 22 s = 15);;
test 168 (below 50 s = 15);;

(* split *)
let splituj x s = let s1,b,s2 = split x s in elements s1, b, elements s2;;
test 172 (splituj (-10) s = ([], false, [(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]));;
test 173 (splituj (-1) s = ([], true, [(0, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]));;
test 174 (splituj 0 s = ([(-1, -1)], true, [(1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]));;
test 175 (splituj 1 s = ([(-1, 0)], true, [(3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]));;
test 176 (splituj 2 s = ([(-1, 1)], false, [(3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)]));;
test 177 (splituj 9 s = ([(-1, 1); (3, 4); (6, 7)], true, [(10, 10); (14, 15); (17, 18); (20, 21)]));;
test 178 (splituj 10 s = ([(-1, 1); (3, 4); (6, 7); (9, 9)], true, [(14, 15); (17, 18); (20, 21)]));;
test 179 (splituj 11 s = ([(-1, 1); (3, 4); (6, 7); (9, 10)], false, [(14, 15); (17, 18); (20, 21)]));;
test 180 (splituj 19 s = ([(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18)], false, [(20, 21)]));;
test 181 (splituj 20 s = ([(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18)], true, [(21, 21)]));;
test 182 (splituj 21 s = ([(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 20)], true, []));;
test 183 (splituj 22 s = ([(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)], false, []));;
test 184 (splituj 25 s = ([(-1, 1); (3, 4); (6, 7); (9, 10); (14, 15); (17, 18); (20, 21)], false, []));;

(* testy na duuuuuże liczby *)
(* za duży przedział i całościowe below *)
let s = add (min_int+5, max_int-7) empty;;
test 189 (below (max_int-3) s = max_int);;

(* pytanie o za duży kawałek *)
test 192 (below 10000 s = max_int);;

(* pytanie o mały kawałek *)
test 195 (below (min_int+20) s = 16);;


(* dwa spore przedziały i całościowy below *)
let s = add (min_int+5, -7) empty;;
let s = add (8, max_int-5) s;;
test 201 (below (max_int-3) s = max_int);;

(* spory kawałek + cały > max_int *)
test 204 (below 10000 s = max_int);;

(* mały kawałek + cały < max_int *)
test 207 (below 16 s = max_int-1);;


(* testy na problemy z maxintami *)
test 211 (elements (add (max_int, max_int) (add (max_int, max_int) empty)) = [(max_int, max_int)]);;

test 213 (elements (add (max_int-1, max_int) (add (max_int, max_int) empty)) = [(max_int-1, max_int)]);;

test 215 (elements (add (max_int, max_int) (add (max_int-1, max_int) empty)) = [(max_int-1, max_int)]);;

test 217 (elements (add (max_int-1, max_int) (add (max_int-1, max_int) empty)) = [(max_int-1, max_int)]);;

test 219 (elements (add (max_int-1, max_int-1) (add (max_int, max_int) empty)) = [(max_int-1, max_int)]);;

test 221 (elements (add (max_int, max_int) (add (max_int-1, max_int-1) empty)) = [(max_int-1, max_int)]);;

test 223 (elements (add (max_int-1, max_int-1) (add (max_int-1, max_int) empty)) = [(max_int-1, max_int)]);;

test 225 (elements (add (max_int-1, max_int) (add (max_int-1, max_int-1) empty)) = [(max_int-1, max_int)]);;


test 228 (elements (add (min_int, min_int) (add (min_int, min_int) empty)) = [(min_int, min_int)]);;

test 230 (elements (add (min_int, min_int+1) (add (min_int, min_int) empty)) = [(min_int, min_int+1)]);;

test 232 (elements (add (min_int, min_int) (add (min_int, min_int+1) empty)) = [(min_int, min_int+1)]);;

test 234 (elements (add (min_int, min_int+1) (add (min_int, min_int+1) empty)) = [(min_int, min_int+1)]);;

test 236 (elements (add (min_int+1, min_int+1) (add (min_int, min_int) empty)) = [(min_int, min_int+1)]);;

test 238 (elements (add (min_int, min_int) (add (min_int+1, min_int+1) empty)) = [(min_int, min_int+1)]);;

test 240 (elements (add (min_int+1, min_int+1) (add (min_int, min_int+1) empty)) = [(min_int, min_int+1)]);;

test 242 (elements (add (min_int, min_int+1) (add (min_int+1, min_int+1) empty)) = [(min_int, min_int+1)]);;


(* od konca do konca *)
test 246 (below max_int (add (min_int, max_int) empty) = max_int);;

println (string_of_int ((below max_int (add (min_int, max_int) empty))));;

assert false;;

(* od srodka do konca *)
test 249 (below 0 (add (min_int, max_int) empty) = max_int);;
test 250 (below 10 (add (min_int, max_int) empty) = max_int);;

(* dwa duże nachodzące *)
test 253 (elements (add (min_int,12) (add (10,max_int) empty)) = [(min_int, max_int)]);;

(* dwa duże ledwo nachodzące *)
test 256 (elements (add (0, max_int) (add (min_int, 0) empty)) = [(min_int, max_int)]);;

(* dwa duże sąsiadujące *)
test 259 (elements (add (0, max_int) (add (min_int, -1) empty)) = [(min_int, max_int)]);;

(* dwa duże rozłączne *)
test 262 (elements (add  (min_int, -12) (add (10,max_int) empty)) = [(min_int,-12); (10,max_int)]);;


(* testy brzegowe na max_int *)
test 266 (below max_int (add (0, max_int) empty) = max_int);;
test 267 (below max_int (add (1, max_int) empty) = max_int);;
test 268 (below max_int (add (2, max_int) empty) = max_int-1);;
test 269 (below max_int (add (-1, max_int-1) empty) = max_int);;
test 270 (below max_int (add (0, max_int-1) empty) = max_int);;
test 271 (below max_int (add (1, max_int-1) empty) = max_int-1);;

test 273 (below (max_int-3) (add (-3, max_int-3) empty) = max_int);;
test 274 (below (max_int-3) (add (-2, max_int-3) empty) = max_int);;
test 275 (below (max_int-3) (add (-1, max_int-3) empty) = max_int-1);;
test 276 (below (max_int-3) (add (-4, max_int-4) empty) = max_int);;
test 277 (below (max_int-3) (add (-3, max_int-4) empty) = max_int);;
test 278 (below (max_int-3) (add (-2, max_int-4) empty) = max_int-1);;

(* max_inty w dużych kawałkach *)
test 281 (below max_int (add (min_int,-2) (add (0,0) (add (2,max_int-10) empty))) = max_int);;
test 282 (below max_int (add (min_int,-2) (add (2,max_int-10) (add (0,0) empty))) = max_int);;
test 283 (below max_int (add (0,0) (add (min_int,-2) (add (2,max_int-10) empty))) = max_int);;
test 284 (below max_int (add (0,0) (add (2,max_int-10) (add (min_int,-2) empty))) = max_int);;
test 285 (below max_int (add (2,max_int-10) (add (min_int,-2) (add (0,0) empty))) = max_int);;
test 286 (below max_int (add (2,max_int-10) (add (0,0) (add (min_int,-2) empty))) = max_int);;



let _ = if !zle = 0 then Printf.printf "Testy poprawnosci OK!\n\n";;


(* testy wydajnosciowe *)

Printf.printf "n' ≈ n/500,  t' ~ t/(n·log n)\n\n";;
    
let dodawaj minim maxim start step s = 
  let rec dod a s = 
    if minim <= a && a <= maxim then 
      dod (a+2*step) (add (min a (a+step), max a (a+step)) s)
    else
      s
  in
  dod start s;;

(* Printf.printf "rrr1: %d rrr2: %d rrr3: %d rrr4: %d\n" (!rrr1) (!rrr2) (!rrr3) (!rrr4);; *)
(* rrr1: 0 rrr2: 0 rrr3: 5 rrr4: 0 *)

let duzedrzewo opis zrob n = 
  let start = Sys.time () in
  let z = zrob n in
  let czas = (Sys.time () -. start) in
  let n' = n / 1000 in
  let f = float_of_int n in
  let t' = czas *. 100000000. /. (f *. log f)  in
  Printf.printf "Budowanie (%s): n'=%5d, t=%2.3f t'=%f\n%!"
    opis n' czas t';
  z

let rosnace n = dodawaj 0 n 0 5 empty
    
let z = duzedrzewo "rosnące" rosnace   625000;;
let z = duzedrzewo "rosnące" rosnace  1250000;;
let z = duzedrzewo "rosnące" rosnace  2500000;;
let z = duzedrzewo "rosnące" rosnace  5000000;;
let z = duzedrzewo "rosnące" rosnace 10000000;;

let start = Sys.time ();;
for i=1 to 10 do
test 330 (below 100000000 z = 6000006);
test 331 (below 10000000 z = 6000001);
test 332 (below 8000000 z = 4800001);
test 333 (below 6000000 z = 3600001);
test 334 (below 4000000 z = 2400001);
test 335 (below 2000000 z = 1200001);
test 336 (below 1000000 z = 600001);
test 337 (below 100000 z = 60001);
test 338 (below 10000 z = 6001);
test 339 (below 1000 z = 601);
test 340 (below 100 z = 61);
test 341 (below 10 z = 7);
test 342 (below 1 z = 2);
test 343 (below (-10) z = 0);
done;;

Printf.printf "Below  (rosnace): %f\n%!" (Sys.time () -. start);;

let start = Sys.time ();;
test 349 (List.length (elements (remove (100, 10000000-100) z)) = 21);;
Printf.printf "Remove (rosnace): %f\n%!" (Sys.time () -. start);;

let start = Sys.time ();;
test 353 (List.length (elements (add (100, 10000000-100) z)) = 21);;
Printf.printf "Add    (rosnace): %f\n%!" (Sys.time () -. start);;

let start = Sys.time ();;
test 357 (fold (fun _ i -> i+1) z 0 = 1000001);;
Printf.printf "Fold   (rosnace): %f\n%!" (Sys.time () -. start);;


(* Printf.printf "rrr1: %d rrr2: %d rrr3: %d rrr4: %d\n" (!rrr1) (!rrr2) (!rrr3) (!rrr4);; *)
(* rrr1: 0 rrr2: 0 rrr3: 49988 rrr4: 0 *)

let skos_lewy n = 
  let z = add (0,0) (add (max_int, max_int) empty) in
  let z = dodawaj 0 n 5 5 z in
  z;;

let z = duzedrzewo "skos_lewy" skos_lewy   625000;;
let z = duzedrzewo "skos_lewy" skos_lewy  1250000;;
let z = duzedrzewo "skos_lewy" skos_lewy  2500000;;
let z = duzedrzewo "skos_lewy" skos_lewy  5000000;;
let z = duzedrzewo "skos_lewy" skos_lewy 10000000;;

let start=Sys.time();;
for i=1 to 10 do
test 377 (below 10000000 z = 6000001);
test 378 (below 8000000 z = 4800001);
test 379 (below 6000000 z = 3600001);
test 380 (below 4000000 z = 2400001);
test 381 (below 2000000 z = 1200001);
test 382 (below 1000000 z = 600001);
test 383 (below 100000 z = 60001);
test 384 (below 10000 z = 6001);
test 385 (below 1000 z = 601);
test 386 (below 100 z = 61);
test 387 (below 10 z = 7);
test 388 (below 1 z = 1);
test 389 (below (-10) z = 0);
done;;

Printf.printf "Below  (skos_lewy): %f\n%!" (Sys.time () -. start);;

let start = Sys.time ();;
test 395 (List.length (elements (remove (100, 10000000-100) z)) = 22);;
Printf.printf "Remove (skos_lewy): %f\n%!" (Sys.time () -. start);;

let start = Sys.time ();;
test 399 (List.length (elements (add (100, 10000000-100) z)) = 22);;
Printf.printf "Add    (skos_lewy): %f\n%!" (Sys.time () -. start);;

let start = Sys.time ();;
test 403 (fold (fun _ i -> i+1) z 0 = 1000002);;
Printf.printf "Fold   (skos_lewy): %f\n%!" (Sys.time () -. start);;

(* Printf.printf "rrr1: %d rrr2: %d rrr3: %d rrr4: %d\n" (!rrr1) (!rrr2) (!rrr3) (!rrr4);; *)
(* rrr1: 191722 rrr2: 8268 rrr3: 99885 rrr4: 0 *)

let skos_prawy n = 
  let z = add (max_int, max_int) (add (0,0) empty) in
  let z = dodawaj 100 n n (-5) z in
  z

let z = duzedrzewo "skos_prawy" skos_prawy   625000;;
let z = duzedrzewo "skos_prawy" skos_prawy  1250000;;
let z = duzedrzewo "skos_prawy" skos_prawy  2500000;;
let z = duzedrzewo "skos_prawy" skos_prawy  5000000;;
let z = duzedrzewo "skos_prawy" skos_prawy 10000000;;


let start = Sys.time ();;
for i=1 to 10 do
test 423 (below 10000000 z = 5999947);
test 424 (below 8000000 z  = 4799947);
test 425 (below 6000000 z  = 3599947);
test 426 (below 4000000 z  = 2399947);
test 427 (below 2000000 z  = 1199947);
test 428 (below 1000000 z = 599947);
test 429 (below 100000 z = 59947);
test 430 (below 10000 z = 5947);
test 431 (below 1000 z = 547);
test 432 (below 100 z = 7);
test 433 (below 10 z = 1);
test 434 (below 1 z = 1);
test 435 (below (-10) z = 0);
done;;  

Printf.printf "Below  (skos_prawy): %f\n%!" (Sys.time () -. start);;

let start = Sys.time ();;
test 441 (below max_int (remove (2, 10000000-1) z) = 3);;
Printf.printf "Remove (skos_prawy): %f\n%!" (Sys.time () -. start);;

let start = Sys.time ();;
test 445 (below max_int (add (2, 10000000-1) z) = 10000001);;
Printf.printf "Add    (skos_prawy): %f\n%!" (Sys.time () -. start);;

let start = Sys.time ();;
test 449 (fold (fun _ i -> i+1) z 0 = 999993);;
Printf.printf "Fold   (skos_prawy): %f\n%!" (Sys.time () -. start);;


let masakra n =
  let z = add (0,0) (add (max_int, max_int) empty) in
  (* dodajemy przedziały [995,1000] [985,990] itd *)
  let z = dodawaj 0 n n (-5) z in
  (* a potem [0,37] [74,111] itd *)
  let z = dodawaj 0 n 0 37 z in
  (* to wymusza sporo łączeń przedziałów... *) 
  z

let z = duzedrzewo "masakra" masakra   625000;;
let z = duzedrzewo "masakra" masakra  1250000;;
let z = duzedrzewo "masakra" masakra  2500000;;
let z = duzedrzewo "masakra" masakra  5000000;;
let z = duzedrzewo "masakra" masakra 10000000;;

let _ = 
  if !zle = 0 then 
    Printf.printf "\nTesty OK!\n"
  else  
    Printf.printf "\nBlednych testow: %d...\n" !zle
;;


(* Printf.printf "rrr1: %d rrr2: %d rrr3: %d rrr4: %d\n" (!rrr1) (!rrr2) (!rrr3) (!rrr4);; *)
(* rrr1: 258234 rrr2: 8268 rrr3: 399763 rrr4: 57 *)

