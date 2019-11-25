(* Typ definujący przedział domknięty [x, y] *)
(* Założenie: x <= y                       *)
type interval = Interval of int * int

(* Porównuje przedziały [al, ar] i [bl, br]     *)
(* Najpier porównuje początki przedziałów       *)
(* a jeśli są takie same to porównuje ich końce *)
(* Zwraca -1 jeśli [al, ar] < [bl, br]          *)
(* Zwraca  0 jeśli  [al, ar] = [bl, br]         *)
(* Zwraca  1 jeśli  [al, ar] = [bl, br]         *)
let cmp (Interval(al, ar)) (Interval(bl, br)) =
    if al < bl then -1
    else if al = bl then (
        if ar < br then -1
        else if ar = br then 0
        else 1)
    else 1

(* Zwraca true jeśli [al, ar] a [bl, br] nachodzą na siebie *)
(* albo są przyległe. W przeciwnym przypadku false           *)
let joint (Interval(al, ar)) (Interval(bl, br)) =
    (ar + 1 >= bl && al <= br + 1) || (br + 1 >= al && bl <= ar + 1)

let str_pair (x, y) =
	"(" ^ (string_of_int x) ^ "; " ^ (string_of_int y) ^ ")"

let rec iterate n (Interval(al, ar)) (Interval(bl, br)) =
	if n = 0 then () else (
		print_string ((str_pair (al, ar)) ^ " " ^ (str_pair (bl, br)) ^ " = ");
		print_string (string_of_int (cmp (Interval(al, ar)) (Interval(bl, br))));
		print_string "\n";
		iterate (n - 1) (Interval(al + 1, ar + 1)) (Interval(bl, br)));;

iterate 20 (Interval(2, 8)) (Interval(10, 16))