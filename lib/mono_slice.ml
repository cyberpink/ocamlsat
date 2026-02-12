module type S = sig
  type t
  type elt
  val make : offset:int -> length:int -> elt array -> t
  val unsafe_make : offset:int -> length:int -> elt array -> t
  val length : t -> int
  val get : t -> int -> elt
  val set : t -> int -> elt -> unit
  val swap : t -> int -> int -> unit
  val iter : (elt -> unit) -> t -> unit
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool
end

module Make(El : sig type t [@@immediate] end) : S with type elt = El.t = struct
  type elt = El.t
  type t = { data : elt array; off : int; length : int }

  let[@inline] unsafe_make ~offset ~length data =
    { data; off = offset; length }

  let make ~offset ~length data =
    let data_len = Array.length data in
    if offset < 0 || offset >= data_len || length > data_len  then
      raise (Invalid_argument "Mono_slice.make");
    { data; off = offset; length }

  let[@inline] length s = s.length
  let[@inline] get s i = Array.unsafe_get s.data (s.off + i)
  let[@inline] set s i l = Array.unsafe_set s.data (s.off + i) l
  let[@inline] swap {data;off;_} i1 i2 =
    let tmp = Array.unsafe_get data (off + i1) in
    Array.unsafe_set data (off + i1) (Array.unsafe_get data (off + i2));
    Array.unsafe_set data (off + i2) tmp

  let iter fn {data;off;length} =
    for i = 0 to length - 1 do
      fn (Array.unsafe_get data (off + i))
    done

  let for_all p {data;off;length}  =
    let stop = off + length in
    let rec loop i =
      if i = stop then true
      else if p (Array.unsafe_get data i) then loop (succ i)
      else false 
    in
    loop off

  let exists p {data;off;length} =
    let stop = off + length in
    let rec loop i =
      if i = stop then false
      else if p (Array.unsafe_get data i) then true
      else loop (succ i)
    in
    loop off
end
