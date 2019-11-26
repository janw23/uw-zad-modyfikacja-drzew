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

(* Zwraca true jeśli [a, b] a [c, d] nachodzą na siebie lub są przyległe *)
let joint (a, b) (c, d) =
    (b + 1 >= c && a <= d + 1) || (d + 1 >= a && c <= b + 1)

(* Zwracają odpowiednio minimum i maksimum z dwóch liczb całkowitych *)
let min (x : int) (y : int) = if x < y then x else y
and max (x : int) (y : int) = if x > y then x else y

(* Łączy dwa przyległe lub nachodzące przedziały w jeden *)
let unify (a, b) (c, d) =
    assert(joint (a, b) (c, d));
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
let bal_fullinfo l k r =
  let hl = height l in
  let hr = height r in
  print_string ("(hl, hr) = (" ^ (string_of_int hl) ^ ", " ^ (string_of_int hr) ^ ")\n");
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _) ->
        if height ll >= height lr then ((make ll lk (make lr k r)), true)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _) ->
              ((make (make ll lk lrl) lrk (make lrr k r)), true)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _) ->
        if height rr >= height rl then ((make (make l k rl) rk rr), true)
        else
          (match rl with
          | Node (rll, rlk, rlr, _) ->
              ((make (make l k rll) rlk (make rlr rk rr)), true)
          | Empty -> assert false)
    | Empty -> assert false
  else ((Node (l, k, r, max hl hr + 1)), false)

(* Wykonuje balansowanie drzewa jeden raz i zwraca nowy set *)
let bal l k r =
	match bal_fullinfo l k r with
	(set,_) -> set

(* Wykonuje balansowanie drzewa tak długo, aż będzie zbalansowane *)
let rec bal_iterate l k r =
	print_string "here\n";
	match bal_fullinfo l k r with
	| (Node(sl, sk, sr, sh), changed) ->
		if changed then bal_iterate sl sk sr
		else Node(sl, sk, sr, sh)
	| (Empty, _) -> assert false

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
      assert(is_balanced (bal_iterate t1 k (remove_min_elt t2)));
      bal_iterate t1 k (remove_min_elt t2)

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

let rec add_one x set = match set with
  | Node (l, k, r, h) ->
      let c = cmp x k in
      if c = 0 then Node (l, x, r, h)
      else if c < 0 then
        let nl = add_one x l in
        bal nl k r
      else
        let nr = add_one x r in
        bal l k nr
  | Empty -> Node (Empty, x, Empty, 1)

let add x set = add_one x set

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

(* Usuwa z set'a wszystkie elementy należące do przedziału [x, y] *)
let remove (x, y) set =
	let l = match split x set with (l,_,_) -> l
	and r = match split y set with (_,_,r) -> r
	in 
		assert(is_balanced (merge l r));
		merge l r

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

(*TODO *)
let below x set = max_int

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

let str_pair (a, b) =
	"(" ^ (string_of_int a) ^ ", " ^ (string_of_int b) ^ ")"

let str_list l =
	let rec helper lst =
		match lst with
		| [] -> "]"
		| h :: [] -> (str_pair h) ^ (helper [])
		| h :: t  -> (str_pair h) ^ "; " ^ (helper t)
	in "[" ^ (helper l)

let print s   = print_string s
and println s = print_string (s ^ "\n");;

let ilst = gen_interval_list 13;;
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
println (str_list (elements (remove (230, 230) iset)));;