
Jakie błędy popełniają studenci:

1. Problemy z max_int / min_int

  Testy 189-229 powinny to wykryć :)

2. Niewłaściwa złożoność różnych operacji

- liniowe remove / add (zwłaszcza te "obejmujące" istniejące przedziały)
  / below

  Testy powinny to wykrywać - jeśli czas jest zbliżony do fold - to
  operacja liniowa, jeśli dużo mniejsza, to log n.

- operacje add / below w czasie (log n)^2

  Serie dla zwiększających się danych mają pomóc zorientować się czy
  wstawianie jest w log n czy (log n)^2 ale nie miałem pod ręką
  takiego przypadku, więc nie wiem... Tam jest wypisywana też wartość
  t/nlogn, która w przypadku n operacji insert powinna być (w
  zasadzie) niezależna od n... - jak wyraźnie rośnie, to może jest
  kwadrat ;)

3. Złe wyważenie drzewa

  To trzeba niestety sprawdzić oczami - problemy głównie wynikają z
  używania merge w sytuacji, gdy różnica w wysokości drzew może być
  dowolna (do tego służy join, ale leniwi/nieuważni studenci zauważają
  tylko, że merge bierze dwa drzewa, a join dwa drzewa i element w
  środek i wybierają to pierwsze...)

  Aby wykazać przykład trzeba stworzyć dość duże drzewo, np
  załączonymi procedurkami...



(* trochę czytelniejsze od standardowego wypisywanie drzewa *)
(*   - oczywiście trzeba dostosować matching do konstruktorów)

let string_of_tree t = 
  let rec fmt_tree fmt = function Empty -> Format.fprintf fmt "Empty"
    | Node (l,(a,b),r,_,_) ->
        Format.fprintf fmt "@[<hv 5>Node(%a,@ (%d,%d),@ %a@,)@]"
          fmt_tree l a b fmt_tree r
  in
  fmt_tree Format.str_formatter t;
  Format.flush_str_formatter ();;

let print_tree t =
  print_string (string_of_tree t);;


(* sprawdz czy drzewo jest zrownoważone *)
let rec check_tree = function Empty -> () | Node (l,(a,b),r,_,_) ->
  let hl, hr = height l, height r in
  let bal = abs (hl - hr) in
  if bal > 2 then (Printf.printf "Niezbalansowane: %d[%d]%d: \n left -> %s\nprzedzial -> (%d, %d)\nright -> %s !!!!\n" hl bal hr (string_of_tree l) a b (string_of_tree r));
  check_tree l;
  check_tree r;;


(* dodawanie przedziałów od start co drugi step ;) aż do wyjścia poza
   minim/maxim *)
   
(* ustaw zrob_lista na true, żeby wypisać dodawane przedziały -
   przydatne, jak się chce studentowi podesłać konkretny przykład *)

let zrob_lista = ref false

let dodawaj minim maxim start step s = 
  let rec dod a s = 
    if minim <= a && a <= maxim then
      let l,r = min a (a+step), max a (a+step) in 
      if !zrob_lista then Printf.printf "(%d,%d); " l r;
      dod (a+2*step) (add (l,r) s)
    else
      s
  in
  dod start s;;


(* drzewa, którymi łapałem większość studentów mających problemy ze
   zrównoważeniem drzewa *)

(* zrób dość duże drzewo - ono ma z 50 węzłów - ma już jakąś konkretną
   głębokość, a jeszcz da się wypisać *)
let z = add (1000,1000) empty;;
let z = dodawaj 0 200 2 2 z;;

check_tree z;;
(* Jest OK *)
print_tree z;;

(* ta operacja zależy od człowieka - czasem add, czasem remove, czasem
wystarczy mały przedział, czasem duży... *)

let sz = remove (129,900) z;;

check_tree sz;;
(* Problem *)
print_tree sz;;
