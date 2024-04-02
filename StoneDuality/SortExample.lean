def mylist := [-8,10,2,3,4]

#check mylist

def sort : List Int -> List Int := by
  intro list
  exact List.reverse list

def sort' (list : List Int) : List Int := List.reverse list

#check sort
#check sort'

#eval sort mylist
#eval sort' mylist

def is_sorted (list : List Int) : Prop := 
  ∀ i < List.length list, ∀ j < List.length list, 
  i < j -> list[i]! <= list[j]!

open List
def reallysort (list : List Int) : 
  { outlist : List Int // is_sorted outlist } := Id.run do
  let mut outlist : List Int := []
  for i in [0 : length list] do
    outlist := outlist.concat i
  return outlist


-- def primes (n : Nat) : Array Nat := Id.run do
--   let mut res : Array Nat := #[]
--   let mut buf : Array Bool := .mkArray n true
--   for i in [2 : n] do
--     if buf[i]! then
--       res := res.push i
--       for j in [i * i : n : i] do
--         buf := buf.set! j false
--   return res
