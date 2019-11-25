(* Porównuje przedziały [a, b] i [c, d]     *)
(* Najpier porównuje początki przedziałów       *)
(* a jeśli są takie same to porównuje ich końce *)
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

(* ----------IMPLEMENTACJA DRZEW AVL---------- *)

(* Typ definiujący dwa rodzaje wierzchołków drzewa tworzącego Set *)
(* Warunek konieczny każdego przedziału [x, y]: x <= y            *)
type t =
    | Empty                              (* Pusty Set *)
    | Node of t * (int * int) * t * int  (* lewe poddrzewo, przedział, prawe poddrzewo, wysokość *)

(* Tworzy pusty Set *)
let empty = Empty

(* Zwraca true, jeśli [set] jest pusty *)
let is_empty (set : t) = s = Empty

(* Zwraca wysokość drzewa *)
let height (_,_,_, h) = h

(* Zwraca najbardziej lewy przedział w drzewie *)
let rec min_elt = function
  | Node (Empty, k, _, _) -> k
  | Node (l, _, _, _) -> min_elt l
  | Empty -> raise Not_found

(*Usuwa najbardziej lewy przedział w drzewie *)
let rec remove_min_elt = function
  | Node (Empty, _, r, _) -> r
  | Node (l, k, r, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "PSet.remove_min_elt"

(* Tworzy nowe drzewo, w którym l r to lewe i prawe *)
(* poddrzewa, k to wartość w nowym korzeniu         *)
let make l k r = Node(l, k, r, max (height l) (height r) + 1)

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

(* Wstawia przedział do drzewa bez sprawdzania, czy ten przedział nachodzi na inne *)
let rec add_one x = function
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

(* Scala dwa drzewa w jedno *)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

(* Łączy dwa drzewa nowym korzeniem o wartości v *)
let rec join l v r =
    match (l, r) with
    | (Empty, _) -> add_one v r
    | (_, Empty) -> add_one v l
    | (Node(ll, lv, lr, lh), Node(rl, rv, rr, rh)) ->
        if lh > rh + 2 then bal ll lv (join lr v r) else
        if rh > lh + 2 then bal (join l v rl) rv rr else
        make l v r

let split x set =
  let rec loop x = function
    | Empty -> (Empty, false, Empty)
    | Node (l, v, r, _) ->
        let c = cmp x v in
        if c = 0 then (l, true, r)
        else if c < 0 then
          let (ll, pres, rl) = loop x l in (ll, pres, join rl v r)
        else
          let (lr, pres, rr) = loop x r in (join l v lr, pres, rr)
  in
  let setl, pres, setr = loop x set in
    (setl, pres, setr)

let rec add (elem : int * int) (set : t) =
    match set with
    | Node (l, k, r, h) ->
        let c = cmp elem k in
        if c = 0 then Node (l, elem, r, h)
        else if c < 0 then
            let nl = add cmp elem l in
            bal nl k r
        else
            let nr = add cmp elem r in
            bal l k nr
    | Empty -> Node (Empty, elem, Empty, 1)

(** [add (x, y) s] returns a set containing the same elements as [s],    plus all elements of the interval [[x,y]] including [x] and [y].
    Assumes [x <= y]. *)

let remove 
(** [remove (x, y) s] returns a set containing the same elements as [s],
    except for all those which are included between [x] and [y].
    Assumes [x <= y]. *)

val mem : int -> t -> bool
(** [mem x s] returns [true] if [s] contains [x], and [false] otherwise. *)

val iter : (int * int -> unit) -> t -> unit
(** [iter f s] applies [f] to all continuous intervals in the set [s].
    The intervals are passed to [f] in increasing order. *)

val fold : (int * int -> 'a -> 'a) -> t -> 'a -> 'a
(** [fold f s a] computes [(f xN ... (f x2 (f x1 a))...)], where x1
    ... xN are all continuous intervals of s, in increasing order. *)

val elements : t -> (int * int) list
(** Return the list of all continuous intervals of the given set.
    The returned list is sorted in increasing order. *)

val below : int -> t -> int
(** [below n s] returns the number of elements of [s] that are lesser
    or equal to [n]. If there are more than max_int such elements, 
    the result should be max_int. *)

val split : int -> t -> t * bool * t
(** [split x s] returns a triple [(l, present, r)], where
    [l] is the set of elements of [s] that are strictly lesser than [x];
    [r] is the set of elements of [s] that are strictly greater than [x];
    [present] is [false] if [s] contains no element equal to [x],
    or [true] if [s] contains an element equal to [x]. *)