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

(* Zwraca true jeśli [a, b] a [c, d] nachodzą na siebie *)
(* lub są przyległe. W przeciwnym przypadku false           *)
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

let slice_left  x (a, _) = (a, x)
and slice_right x (_, b) = (x, b)

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
			in (max l_first r_first + 1, l_second && r_second && (abs (l_first - r_first) <= 2))
	in match helper set with (_, res) -> res

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
  | Node (l, k, r, _) -> bal (remove_min_elt l) k r
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

let rec join l v r =
  match (l, r) with
    (Empty, _) -> add_one v r
  | (_, Empty) -> add_one v l
  | (Node(ll, lv, lr, lh), Node(rl, rv, rr, rh)) ->
      if lh > rh + 2 then bal ll lv (join lr v r) else
      if rh > lh + 2 then bal (join l v rl) rv rr else
      make l v r

(* Dostaje liczbę [x] oraz drzewo [set] 												   *)
(* Zwraca trójkę: (drzewo elementów < [x], czy [set] zawiera [x]?, drzewo elementów > [x]) *)
(* TODO: Sprawdzić, czy to działa *)
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

let remove x set =
  let rec loop = function
    | Node (l, k, r, _) ->
        let c = cmp x k in
        if c = 0 then merge l r else
        if c < 0 then bal (loop l) k r else bal l k (loop r)
    | Empty -> Empty in
      loop set

let mem x set = true
  (*let rec loop = function
    | Node (l, k, r, _) ->
        let c = cmp x k in
        c = 0 || loop (if c < 0 then l else r)
    | Empty -> false in
  loop set*)

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

let below x set = max_int

let elements set = 
  let rec loop acc = function
      Empty -> acc
    | Node(l, k, r, _) -> loop (k :: loop acc r) l in
  loop [] set;;