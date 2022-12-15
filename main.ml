type formula =
    Var of int
  | Not of formula
  | Or of formula * formula
  | And of formula * formula
  | Imply of formula * formula
  | Top
  | Bottom
  
type valuation = int * bool list

let f1 = Imply (Var 4, Imply (Imply (Var 3, Var 2), Var 1))
let f2 = Or (And (Var 1, Imply (Var 2, Var 3)), Bottom)
let f3 = Or (Imply (Var 6, Var 5), Or (And (Var 3, Or (Var 4, Var 3)), And (Var 1, Var 5)))

let rec formula_height = function
  | Var _ | Bottom | Top -> 1
  | Not f -> 1 + formula_height f
  | Or (f1, f2) | And (f1, f2) | Imply (f1, f2) -> 1 + max (formula_height f1) (formula_height f2)

let rec size = function
  | Var _ | Bottom | Top -> 1
  | Not f -> 1 + size f
  | Or (f1, f2) | And (f1, f2) | Imply (f1, f2) -> 1 + (size f1) + (size f2)

let rec get_value v i = match v with
  | [] -> false
  | ((ind, b) :: t) -> if i == ind then b else get_value t i

let rec evaluate f v = match f with
  | Top -> true
  | Bottom -> false
  | Not f -> not (evaluate f v)
  | And (f1, f2) -> (evaluate f1 v) && (evaluate f2 v)
  | Or (f1, f2) -> (evaluate f1 v) || (evaluate f2 v)
  | Imply (f1, f2) -> (not (evaluate f1 v)) || (evaluate f2 v)
  | Var i -> get_value v i

let v = [(1, true); (2, false); (3, false)];;

let rec variable_list = function
  | Var i -> [i]
  | And (f1, f2) | Or (f1, f2) | Imply (f1, f2) ->  (variable_list f1) @ (variable_list f2)
  | Not f -> variable_list f
  | _ -> []

let generate_all_valuations indices = 
  let add acc i = 
    (List.map (fun li -> (i, false) :: li) acc) @ (List.map (fun li -> (i, true) :: li) acc)
  in List.fold_left add [[]] indices;;

let values f = f |> variable_list |> generate_all_valuations |> List.map (evaluate f)

let is_satisfiable f = List.exists (Fun.id) (values f)

let is_contradiction f = List.for_all (not) (values f)

let is_tautology f = List.for_all (Fun.id) (values f)

let is_equivalent f1 f2 = 
  let valuations =  ((variable_list f1) @ (variable_list f2)) |> List.sort_uniq (-) |> generate_all_valuations in
  List.equal (==) (List.map (evaluate f1) valuations) (List.map (evaluate f2) valuations)

let print_truth_table f = 
  let variables = List.sort_uniq (-) (variable_list f) in
  let valuations = generate_all_valuations variables in
  let header = String.cat (String.concat "|" (List.map string_of_int variables)) "|=" in
  let get_valuation_line f v = String.cat (String.concat "|" (List.map (fun (i, b) -> if b then "1" else "0") v)) (if evaluate f v then "|1" else "|0") in
  let table = String.concat "\n" (List.map (get_valuation_line f) valuations) in
  print_endline (String.concat "\n" [header;table])

let rec subformulas f = match f with
  | Var _ | Bottom | Top -> [f]
  | Not f' -> f :: subformulas f'
  | Or (f1, f2) | And (f1, f2) | Imply (f1, f2) -> f :: (subformulas f1 @ subformulas f2)

let rec substitute f i f' = match f with
  | Var p -> if p == i then f' else f
  | Top | Bottom -> f
  | Not f1 -> Not (substitute f1 i f')
  | And (f1, f2) -> And (substitute f1 i f', substitute f2 i f')
  | Or (f1, f2) -> Or (substitute f1 i f', substitute f2 i f')
  | Imply (f1, f2) -> Imply (substitute f1 i f', substitute f2 i f')

let substitution = substitute f1 4 Bottom;;

let rec simplify f = match f with
  | Bottom | Top | Var _ -> f
  | And (f1, f2) -> let (s1, s2) = (simplify f1, simplify f2) in (match (s1, s2) with
    | (Top, Top) -> Top
    | (Bottom, _) -> Bottom
    | (_, Bottom) -> Bottom
    | (s1, s2) -> And (s1, s2))
  | Or (f1, f2) -> let (s1, s2) = (simplify f1, simplify f2) in (match (s1, s2) with
    | (Bottom, Bottom) -> Top
    | (Top, _) -> Top
    | (_, Top) -> Top
    | (s1, s2) -> Or (s1, s2))
  | Imply (f1, f2) -> let (s1, s2) = (simplify f1, simplify f2) in (match (s1, s2) with
    | (Bottom, _) -> Top
    | (Top, v) -> v
    | (s1, s2) -> Imply (s1, s2))
  | Not f' -> let s = simplify f' in (match s with
    | Top -> Bottom 
    | Bottom -> Top
    | Not (Not v) -> v
    | v ->  s)

let rec quine f = let q = simplify f in 
  match List.sort_uniq (-) (variable_list q) with
    | v :: t -> 
      let tf = substitute q v Top in 
      let bf = substitute q v Bottom in
      quine tf || quine bf
    | [] -> q = Top

let toDNF f = 
  let vars = f |> variable_list |> List.sort_uniq (-) in
  let valuations = vars |> generate_all_valuations |> List.filter (evaluate f) in
  let rec kminterm valuation = match valuation with
    | [] -> Top
    | (i, true) :: [] -> Var i
    | (i, false) :: [] -> Not (Var i)
    | (i, true) :: t -> And (Var i, kminterm t)
    | (i, false) :: t -> And (Not (Var i), kminterm t)
  in
  let rec dnf vals = match vals with
    | [] -> Bottom
    | v :: [] -> kminterm v
    | v :: t -> Or (kminterm v, dnf t)
  in dnf valuations

let toCNF f = 
  let notDNF = toDNF (Not f) in 
  let rec notDeMorgan f = match f with
    | Not f -> f
    | Or (f1, f2) -> And (notDeMorgan f1, notDeMorgan f2)
    | And (f1, f2) -> Or (notDeMorgan f1, notDeMorgan f2)
    | f -> Not f
  in notDeMorgan notDNF