module Main

open FStar.Exn
open FStar.All

type filename = string

let canWrite (f : filename) =
  match f with
  | "demo/tempfile" -> true
  | _ -> false

let canRead (f : filename) : Tot bool =
  canWrite f || f = "demo/README"

let read (f : filename{canRead f}) : ML string =
  FStar.IO.print_string ("Dummy read of file ''" ^ f ^ "'\n");
  f

let write (f : filename{canWrite f}) (s : string) : ML unit =
  FStar.IO.print_string ("Dummy write of string ''" ^ s ^ "'' to file ''" ^ f ^ "'\n")

let passwd : filename = "demo/password"
let readme : filename = "demo/README"
let tmp    : filename = "demo/tempfile"

exception InvalidRead
val checkedRead : filename -> ML string
let checkedRead f =
  if canRead f then read f else raise InvalidRead

exception InvalidWrite
val checkedWrite : filename -> string -> ML unit
let checkedWrite f s =
  if canWrite f then write f s else raise InvalidWrite

val staticChecking : unit -> ML unit
let staticChecking () =
  let v1 = read tmp in
  let v2 = read readme in
  let v3 = checkedRead passwd in // invalid read, fails type-checking
  write tmp "hello!";
  checkedWrite passwd "junk" // invalid write , fails type-checking

val append : #a:Type -> list a -> list a -> Tot (list a)
let rec append #a l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append #a tl l2

let rec length (l : list 'a) : nat =
  match l with
  | [] -> 0
  | _ :: l -> 1 + length l

let rec append_length (l1 l2 : list 'a) : Lemma (length (append l1 l2) = length l1 + length l2) =
  match l1 with
  | [] -> ()
  | _ :: l1 -> append_length l1 l2

let project_cons_head (l : list 'a{Cons? l}) : 'a =
  match l with
  | x :: _ -> x
