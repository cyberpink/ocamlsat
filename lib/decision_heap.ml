open Common

type t = {
  heap : int array;
  pos : int array;
  activity : Float.Array.t;
  mutable size : int;
  mutable inc : float;
}
let invalid_pos = -1

let create nvars = {
  heap = Array.make nvars 0;
  pos = Array.make nvars invalid_pos;
  activity = Float.Array.make nvars 0.0;
  size = 0;
  inc = 1.0;
}
let swap t i j =
  let v_i = t.heap.(i) in
  let v_j = t.heap.(j) in
  t.heap.(i) <- v_j;
  t.heap.(j) <- v_i;
  t.pos.(v_i) <- j;
  t.pos.(v_j) <- i

let (.%()) = Float.Array.unsafe_get
let (.%()<-) = Float.Array.unsafe_set
let higher_priority t i j =
  let v_i = t.heap.(i) in
  let v_j = t.heap.(j) in
  t.activity.%(v_i) > t.activity.%(v_j)

let rec sift_up t i =
  if i > 0 then
    let parent = (i - 1) / 2 in
    if higher_priority t i parent then begin
      swap t i parent;
      sift_up t parent
    end

let rec sift_down t i =
  let left = 2 * i + 1 in
  let right = left + 1 in
  let largest =
    if left < t.size && higher_priority t left i then left else i
  in
  let largest =
    if right < t.size && higher_priority t right largest then right else largest
  in
  if largest <> i then begin
    swap t i largest;
    sift_down t largest
  end

let contains t v = t.pos.(Var.to_int v) <> invalid_pos
let insert t v =
  let v' = Var.to_int v in
  if t.pos.(v') = invalid_pos then begin
    let i = t.size in
    t.heap.(i) <- v';
    t.pos.(v') <- i;
    t.size <- t.size + 1;
    sift_up t i
  end

let pop_max t =
  if t.size = 0 then None
  else
    let root = t.heap.(0) in
    let last_idx = t.size - 1 in
    let last_val = t.heap.(last_idx) in
    (* set new root *)
    t.heap.(0) <- last_val;
    t.pos.(last_val) <- 0;
    (* remove old root *)
    t.pos.(root) <- invalid_pos;
    t.size <- t.size - 1;
    if t.size > 1 then sift_down t 0;      
    Some (Var.of_int root)

(* VSIDS specific *)
let rescale_threshold = 1e100
let rescale_factor = 1e-100
let decay_inv = 1.0 /. 0.95
let rescale t =
  t.inc <- t.inc *. rescale_factor;
  for i = 0 to Float.Array.length t.activity - 1 do
    t.activity.%(i) <- rescale_factor *. t.activity.%(i)
  done

let bump t v =
  let v' = Var.to_int v in
  t.activity.%(v') <- t.activity.%(v') +. t.inc;
  if t.activity.%(v') > rescale_threshold then rescale t;
  if contains t v then sift_up t t.pos.(v')

let decay_activity t = t.inc <- t.inc *. decay_inv
