module HW2 (
    parse, -- reexport for easy terminal use
    foldAndPropagateConstants,
    assignCommonSubexprs,
    reducePoly
) where

import Expression
import Parser
import Data.List

-- Do not change the module definition and imports above! Feel free
-- to modify the parser, import other modules, especially Data.List!


isConstLeaf :: ExprV -> Bool
isConstLeaf (Leaf (Constant _)) = True
isConstLeaf _ = False
fetchValue :: ExprV -> Int
fetchValue (Leaf (Constant a)) = a
isLeaf :: ExprV -> Bool
isLeaf (Leaf _) = True
isLeaf _ = False
isUnary :: ExprV -> Bool
isUnary (UnaryOperation Minus (t)) = True
isUnary _ = False
isConstUnary :: ExprV -> Bool
isConstUnary (UnaryOperation Minus (Leaf (Constant a))) = True
isConstUnary _ = False
fetchValue2 :: ExprV -> Int
fetchValue2 (UnaryOperation Minus (Leaf (Constant a))) = -1*a
isVarUnary :: ExprV -> Bool
isVarUnary (UnaryOperation Minus (Leaf (Variable a))) = True
isVarUnary _ = False
combine:: [(String, ExprV)] -> [(String, ExprV)] -> [(String, ExprV)] 
combine x y = nub (x ++ y)

foldAndPropagateConstants :: [(String, ExprV)] -> [(String, ExprV)]
foldAndPropagateConstants [] = []
foldAndPropagateConstants (x:xs) = foldAndPropagateConstants2 (x:xs) []

foldAndPropagateConstants2 :: [(String, ExprV)] ->[(String, Int)] -> [(String, ExprV)]
foldAndPropagateConstants2 [] _ = []
foldAndPropagateConstants2 (x:xs) (read_list) = 
                               if (isLeaf (snd x)) then if (isConstLeaf (snd x)) then ((fst x), snd x):(foldAndPropagateConstants2 (xs) ((fst x, (fetchValue (snd x))): read_list))
                                                                                 else let unknown=(traverse' (fst x) (snd x) (read_list))   
                                                                                      in if (isConstLeaf (fst unknown)) then ((fst x), (fst unknown)):(foldAndPropagateConstants2 (xs) ((fst x, (fetchValue (fst unknown))): read_list))              
                                                                                                                        else ((fst x), (fst unknown)):(foldAndPropagateConstants2 (xs) (read_list))
                                                   else if (isUnary (snd x)) then if (isConstUnary (snd x)) then ((fst x), (Leaf (Constant (fetchValue2 (snd x))))):(foldAndPropagateConstants2 (xs) ((fst x, (fetchValue2 (snd x))): read_list))
                                                                                                            else let unknown=(traverse' (fst x) (snd x) (read_list))   
                                                                                                                 in if (isConstLeaf (fst unknown)) then ((fst x), (fst unknown)):(foldAndPropagateConstants2 (xs) ((fst x, (fetchValue2 (fst unknown))): read_list))              
                                                                                                                                                   else ((fst x), (fst unknown)):(foldAndPropagateConstants2 (xs) (read_list))



                                                                           else let res=(traverse' (fst x) (snd x) (read_list))
                                                                                    exprv = (fst res)
                                                                                    new_list= snd res
                                                                                in ((fst x), exprv):(foldAndPropagateConstants2 (xs) (new_list))


find_in_read_list :: String -> [(String, Int)] -> [Int]
find_in_read_list (name) [] = []
find_in_read_list (name) (x:xs) = if ((fst x)==(name)) then [snd x] 
                                                       else find_in_read_list (name) (xs)


traverse' :: String -> ExprV -> [(String, Int)] -> (ExprV,[(String, Int)])

traverse' (name) (Leaf (Constant a)) (read_list) = ((Leaf (Constant a)),(read_list)) 
traverse' (name) (Leaf (Variable a)) (read_list) = let temp= (find_in_read_list (a) (read_list))
                                                   in if temp/=[] then (Leaf (Constant (head (temp))),(read_list)) 
                                                                  else (Leaf (Variable a),(read_list))
                                                                    
traverse' (name) (UnaryOperation Minus (Leaf (Constant a))) (read_list) = ((Leaf (Constant (-a))),(read_list))
traverse' (name) (UnaryOperation Minus (Leaf (Variable a))) (read_list) = let temp= (find_in_read_list (a) (read_list))
                                                                          in if temp/=[] then (Leaf (Constant (-1*(head (temp)))),(read_list)) 
                                                                                         else ((UnaryOperation Minus (Leaf (Variable a))),(read_list))
traverse' (name) (UnaryOperation Minus (UnaryOperation Minus (t))) (read_list) = let res= (traverse' (name) (t) read_list)
                                                                                 in if (isConstLeaf (fst res)) then ((Leaf (Constant (fetchValue (fst res)))),(snd res)) 
                                                                                                               else ((UnaryOperation Minus (UnaryOperation Minus (fst res))),(snd res))
traverse' (name) (UnaryOperation Minus (BinaryOperation oprtr (left) (right))) (read_list) = 
                  let res=traverse' (name) (BinaryOperation oprtr (left) (right)) (read_list)
                  in if (isLeaf (fst res)) then (traverse' (name) (UnaryOperation Minus (fst res)) (snd res))                                                 
                                           else (UnaryOperation Minus (fst res) ,(snd res))
                                                                                                                                                                                                                                                                                                            
traverse' (name) (BinaryOperation oprtr (left) (right)) (read_list) =
      let
         l = fst (traverse' (name) (left) (read_list))
         r = fst (traverse' (name) (right) (read_list))
      in if (isConstLeaf (l) && isConstLeaf (r))   
                            then let operation = if (oprtr == Times) then (*) else (+)
                                     a = fetchValue (l) `operation` fetchValue (r)
                                     new_readlist = (name, a) : read_list
                                 in (Leaf (Constant a),(new_readlist))                             
                            else ((BinaryOperation oprtr (l) (r)),(read_list))     

assignCommonSubexprs :: ExprV -> ([(String, ExprV)], ExprV)
assignCommonSubexprs exprv = iteration_func exprv []


iteration_func exprv list =  let list_of_expressions= (detector' exprv [])
                                 my_tree_and_list= tree_update exprv list_of_expressions list
                                 last_list= list1_filter (fst my_tree_and_list)
                             in if (exprv==snd (my_tree_and_list)) then (last_list , snd my_tree_and_list) 
                                                                   else (iteration_func (snd (my_tree_and_list)) last_list)                          

list1_filter ::  [(String, ExprV)] -> [(String, ExprV)]
list1_filter [] = []
list1_filter all@(x:xs) = let element = lowest_one (all)
                          in (element: (list1_filter (discard_lowest (element) all)))

                 
discard_lowest :: (String, ExprV) -> [(String, ExprV)] ->   [(String, ExprV)] 
discard_lowest found [] = []
discard_lowest found (x:xs) = if (found ==x) then (xs) else (x: (discard_lowest found xs))

lowest_one ::  [(String, ExprV)] -> (String, ExprV)                                    
lowest_one [x] = x
lowest_one (x:xs) = if ((fst x )<(fst (head xs))) then lowest_one (x: (drop 1 (xs))) else (lowest_one (xs))



find_in_read_list2 ::  ExprV -> [(String, ExprV)] -> String
find_in_read_list2 exprv [] = "null"
find_in_read_list2 exprv (x:xs) = if ((snd x)==(exprv)) then (fst (x))
                                                       else find_in_read_list2 exprv (xs)
how_many_in_read_list ::  ExprV -> [ExprV] -> Int
how_many_in_read_list exprv [] = 0
how_many_in_read_list exprv (x:xs) = if (x==(exprv))  then 1+ how_many_in_read_list exprv (xs)
                                                      else how_many_in_read_list exprv (xs)


detector' :: ExprV -> [ExprV] ->  [ExprV]

detector' (Leaf (Constant a)) (temp_list)  =   (temp_list)
detector' (Leaf (Variable a)) (temp_list) =  (temp_list)
                                                                    
detector' (UnaryOperation Minus (Leaf t)) (temp_list) = 
      let new_temp_list = ((UnaryOperation Minus (Leaf t)) : temp_list)
      in  (new_temp_list)

detector' (UnaryOperation Minus (BinaryOperation oprtr (left) (right))) (temp_list) = 
      (UnaryOperation Minus (BinaryOperation oprtr (left) (right))) : (detector' (BinaryOperation oprtr (left) (right)) (temp_list))
detector' (UnaryOperation Minus (UnaryOperation Minus x)) (temp_list) = 
      (UnaryOperation Minus (UnaryOperation Minus x)) : (detector' (UnaryOperation Minus x) (temp_list))

detector' (BinaryOperation oprtr (Leaf x) (Leaf y)) (temp_list) =
      let new_temp_list = ((BinaryOperation oprtr (Leaf x ) (Leaf y )) : temp_list)
      in (new_temp_list)
detector' (BinaryOperation oprtr (left) (right)) (temp_list) =
      let l=detector' left (temp_list) 
          r=detector' right (temp_list)
          union_temp_list= (BinaryOperation oprtr (left) (right)) : (l ++ r)
      in (union_temp_list)

tree_update :: ExprV -> [ExprV] -> [(String, ExprV)] -> ([(String, ExprV)], ExprV)

tree_update (Leaf (Constant a)) (temp_list) (new_list) =  (new_list, (Leaf (Constant a)))
tree_update (Leaf (Variable a)) (temp_list) (new_list) = (new_list, (Leaf (Variable a)))
                                                                    
tree_update (UnaryOperation Minus (Leaf x)) (temp_list) (new_list) = 
      let temp = how_many_in_read_list (UnaryOperation Minus (Leaf x)) (temp_list)
      in if (temp>1) then let found_name = find_in_read_list2 (UnaryOperation Minus (Leaf x)) (new_list)
                          in if (found_name/="null") then ((new_list),  (Leaf (Variable found_name))) 
                                                     else let name= ("$" ++ (show (length (new_list))))
                                                              updated_list= (name,(UnaryOperation Minus (Leaf x))) : (new_list)
                                                          in ((updated_list), (Leaf (Variable name))) 
                     else ((new_list), (UnaryOperation Minus (Leaf x)))

tree_update (UnaryOperation Minus (UnaryOperation Minus x)) (temp_list) (new_list) =
      let inner=(UnaryOperation Minus x) 
          incoming_res= (tree_update (inner) (temp_list) (new_list))
      in if ((isLeaf (snd incoming_res))==True) then (tree_update (UnaryOperation Minus (snd incoming_res)) (temp_list) (fst incoming_res))
                                          else (fst incoming_res ,(UnaryOperation Minus (snd incoming_res)))
tree_update (UnaryOperation Minus (BinaryOperation oprtr (left) (right))) (temp_list) (new_list) =
      let res=(tree_update (BinaryOperation oprtr (left) (right)) (temp_list) (new_list))
          incoming_list= fst res
          incoming_tree= snd res
          temp = how_many_in_read_list (UnaryOperation Minus ((BinaryOperation oprtr (left) (right)))) (temp_list)
      in if ((temp>1) && ((isLeaf (incoming_tree))==True)) then let found_name = find_in_read_list2 (UnaryOperation Minus (incoming_tree)) (incoming_list)
                                                                in if (found_name/="null") then ((incoming_list),  (Leaf (Variable found_name))) 
                                                                                         else let name= ("$" ++ (show (length (incoming_list))))
                                                                                                  updated_list= (name,(UnaryOperation Minus (incoming_tree))) : (incoming_list)
                                                                                              in ((updated_list), (Leaf (Variable name))) 
                                                           else (incoming_list, (UnaryOperation Minus (incoming_tree)))

tree_update (BinaryOperation oprtr (Leaf x ) (Leaf y)) (temp_list) (new_list) =
      let temp = how_many_in_read_list (BinaryOperation oprtr (Leaf x ) (Leaf y)) (temp_list)
      in if (temp>1) then let found_name = find_in_read_list2 (BinaryOperation oprtr (Leaf x ) (Leaf y)) (new_list)
                          in if (found_name/="null") then ((new_list),  (Leaf (Variable found_name))) 
                                                     else let name= ("$" ++ (show (length (new_list))))
                                                              updated_list= (name,(BinaryOperation oprtr (Leaf x ) (Leaf y))) : (new_list)
                                                          in ((updated_list), (Leaf (Variable name))) 
                     else ((new_list), (BinaryOperation oprtr (Leaf x ) (Leaf y)))

tree_update (BinaryOperation oprtr (left) (right)) (temp_list) (new_list) =
      let l= tree_update left (temp_list) (new_list)
          r= tree_update right (temp_list) (fst l)
          union_new_list = combine (fst (l))  (fst (r))
      in if (snd l == snd r && ((isLeaf (snd l) && isLeaf (snd r))==False)) then let name= ("$" ++ (show (length (union_new_list))))
                                                                                     updated_list= (name, snd l) : (union_new_list)
                                                                                 in ((updated_list), (BinaryOperation oprtr (Leaf (Variable name)) (Leaf (Variable name)))) 
                                                                            else (union_new_list,(BinaryOperation oprtr (snd l) (snd r)))

name_search :: ExprV -> String
name_search (Leaf (Constant a)) = "null"
name_search (Leaf (Variable a)) = a
name_search (UnaryOperation Minus (Leaf (Variable a))) = a
name_search (UnaryOperation Minus (Leaf (Constant a))) = "null"
name_search (UnaryOperation Minus (UnaryOperation Minus (t))) = name_search (UnaryOperation Minus (t))
name_search (UnaryOperation Minus (BinaryOperation oprtr (left) (right))) = let lft = (name_search (left))
                                                                                rt = (name_search (right))
                                                                            in if (lft /="null" || rt=="null") then lft else if (lft =="null" || rt/="null") then rt else "null"
name_search (BinaryOperation oprtr (left) (right)) =  let lft = (name_search (left))
                                                          rt = (name_search (right))
                                                      in if (lft /="null" || rt=="null") then lft else if (lft =="null" || rt/="null") then rt else "null"


reducePoly :: ExprV -> ExprV
reducePoly exprv = 
          let my_poly= (exprv_to_poly (exprv))
              name= (name_search (exprv))
              my_result= poly_to_exprv (name) (my_poly)
          in (zero_converter my_result)

zero_converter (Leaf (Constant a)) = (Leaf (Constant a))
zero_converter (Leaf (Variable a)) = (Leaf (Variable a))
zero_converter (UnaryOperation Minus (Leaf (Variable a))) = (UnaryOperation Minus (Leaf (Variable a)))
zero_converter (UnaryOperation Minus (Leaf (Constant a))) = (UnaryOperation Minus (Leaf (Constant a)))
zero_converter (UnaryOperation Minus (UnaryOperation Minus (t))) = (UnaryOperation Minus (zero_converter (UnaryOperation Minus (t))))
zero_converter (UnaryOperation Minus (BinaryOperation oprtr (left) (right))) = (UnaryOperation Minus (zero_converter (BinaryOperation oprtr (left) (right))))
zero_converter (BinaryOperation oprtr (left) (right)) =  
    let lft = (zero_converter (left))
        rt= (zero_converter (right))
    in if (oprtr==Times) then if (lft==(Leaf (Constant 0)) || lft==(UnaryOperation Minus (Leaf (Constant 0)))  || rt==(Leaf (Constant 0)) || rt==(UnaryOperation Minus (Leaf (Constant 0)))) 
                              then (Leaf (Constant 0))  else (BinaryOperation oprtr (lft) (rt))
                         else if ((lft==(Leaf (Constant 0)) && rt==(Leaf (Constant 0))) || (lft==(UnaryOperation Minus (Leaf (Constant 0))) && rt==(Leaf (Constant 0))) || (lft==(Leaf (Constant 0)) && rt==(UnaryOperation Minus (Leaf (Constant 0)))) || (lft==(UnaryOperation Minus (Leaf (Constant 0))) && rt==(UnaryOperation Minus (Leaf (Constant 0)))) )
                                                                                       then (Leaf (Constant 0))
                                                                                       else if (lft==(Leaf (Constant 0))) then (rt) 
                                                                                                                          else if (rt==(Leaf (Constant 0))) then (lft)
                                                                                                                                                            else  (BinaryOperation oprtr (lft) (rt))
data Polynomial = E | Polynomial (Int, Int, Polynomial) deriving (Eq, Read, Show)

get_fst (Polynomial (a, _, _)) = a
get_snd (Polynomial (_, a, _)) = a
get_trd (Polynomial (_, _, a)) = a

add_Poly (E) (Polynomial (cns2, exp2, _)) = E

add_Poly (Polynomial (cns1, exp1, E)) (E) =  (Polynomial (cns1, exp1, E))
add_Poly (Polynomial (cns1, exp1, E)) (Polynomial (cns2, exp2, rest2)) = 
     if (cns1+cns2==0) then (rest2)
                       else if (exp1==exp2) then (Polynomial ((cns1+cns2),exp1,rest2))
                                            else (Polynomial (cns2, exp2, (add_Poly (Polynomial (cns1, exp1, E)) (rest2))))
                                  
add_Poly (Polynomial (cns1, exp1, rest1)) (Polynomial (cns2, exp2, rest2)) = 
                    let element= (Polynomial (cns1, exp1, E))
                        result= (add_Poly (element) (Polynomial (cns2, exp2, rest2)))
                    in (add_Poly rest1 result  )
 
 
multiply_Poly (E) (Polynomial (cns2, exp2, _)) = (E)
multiply_Poly (Polynomial (cns1, exp1, E))  E  =  E
multiply_Poly (Polynomial (0, exp1, E))  (Polynomial (cns2, exp2, rest2))  =  (Polynomial (0, 0, E))
multiply_Poly (Polynomial (cns1, exp1, E)) (Polynomial (cns2, exp2, rest2)) = 
     if ( exp1/=0 && exp2/=0 ) then (Polynomial (cns1*cns2, exp1+exp2,(multiply_Poly (Polynomial (cns1, exp1, E)) rest2 ))) 
                               else if (exp1==0 && exp2/=0) then (Polynomial (cns1*cns2, exp2,(multiply_Poly (Polynomial (cns1, exp1, E)) rest2 ))) 
                                                            else (Polynomial (cns1*cns2, exp1,(multiply_Poly (Polynomial (cns1, exp1, E)) rest2 ))) 

multiply_Poly (Polynomial (cns1, exp1, rest1)) (Polynomial (cns2, exp2, rest2)) = 
                    let element= (Polynomial (cns1, exp1, E))
                        result= (multiply_Poly (element) (Polynomial (cns2, exp2, rest2)))
                    in (add_Poly (result) (multiply_Poly rest1  (Polynomial (cns2, exp2, rest2))) )

exprv_to_poly (Leaf (Constant a)) = Polynomial (a,0,E)
exprv_to_poly (Leaf (Variable a)) = Polynomial (1,1,E)
exprv_to_poly (UnaryOperation Minus (Leaf (Constant a))) = Polynomial (-a,0,E)
exprv_to_poly (UnaryOperation Minus (Leaf (Variable a))) = Polynomial (-1,1,E)
exprv_to_poly (UnaryOperation Minus (UnaryOperation Minus  (t))) = (multiply_Poly (Polynomial (-1, 0, E)) (exprv_to_poly (UnaryOperation Minus  (t))))
exprv_to_poly (UnaryOperation Minus (BinaryOperation oprtr (left) (right))) = if (oprtr == Times) then let res= (multiply_Poly (exprv_to_poly (left)) (exprv_to_poly (right)))
                                                                                                       in (multiply_Poly  (Polynomial ((-1),0,E)) res)
                                                                                                  else let res= add_Poly (exprv_to_poly (left)) (exprv_to_poly (right))
                                                                                                       in (multiply_Poly  (Polynomial ((-1),0,E)) res)

exprv_to_poly (BinaryOperation oprtr (left) (right)) = if (oprtr == Times) then multiply_Poly (exprv_to_poly (left)) (exprv_to_poly (right))
                                                                           else add_Poly (exprv_to_poly (left)) (exprv_to_poly (right))

poly_to_exprv (name) (Polynomial (-1,1,E)) = (UnaryOperation Minus (Leaf (Variable (name))))
poly_to_exprv (name) (Polynomial (c,0,E)) = (Leaf (Constant c)) 
poly_to_exprv (name) (Polynomial (c,1,E)) = if c==1 then (Leaf (Variable (name))) 
                                                    else (BinaryOperation Times (Leaf (Constant c)) (Leaf (Variable (name))))

poly_to_exprv (name) (Polynomial (c,expo,E)) = if c/=1 then if c>1 then multiplication_converter (name) (BinaryOperation Times (Leaf (Constant c)) (Leaf (Variable (name)))) (expo-1) 
                                                                   else if c==(-1) then multiplication_converter (name) (UnaryOperation Minus (Leaf (Variable (name)))) (expo-1)
                                                                                   else multiplication_converter (name) (BinaryOperation Times (Leaf (Constant c)) (Leaf (Variable (name)))) (expo-1)                                                           
                                                       else multiplication_converter (name) (BinaryOperation Times (Leaf (Variable (name))) (Leaf (Variable (name)))) (expo-2)

poly_to_exprv (name) (Polynomial (a,b,(Polynomial (x,y,rest)))) = 
                      let ordered_poly= order_expo (Polynomial (a,b,(Polynomial (x,y,rest))))
                          (n1, n2,n3)=(get_fst ordered_poly, get_snd ordered_poly, get_trd ordered_poly)
                          single1=(Polynomial (n1,n2,E))
                          single2=(Polynomial (get_fst n3, get_snd n3, E))
                          first_two=(BinaryOperation Plus (poly_to_exprv (name) single1) (poly_to_exprv (name) single2))
                      in if (is_empty n3) then first_two else sum_converter name (first_two) (get_trd n3)
multiplication_converter :: String -> ExprV -> Int -> ExprV
multiplication_converter name exprv 0 = exprv
multiplication_converter name exprv expo = multiplication_converter (name) (BinaryOperation Times (exprv) (Leaf (Variable (name)))) (expo-1)

sum_converter name exprv (E) = exprv
sum_converter name exprv (Polynomial (x,y,rest)) = let converted_elm = (poly_to_exprv (name) (Polynomial (x,y,E)))
                                                       update= (BinaryOperation Plus (exprv) (converted_elm))
                                                   in (sum_converter name update (rest))
   
is_empty (Polynomial (_,_,E)) = True
is_empty (Polynomial (_,_,_)) = False

lowest_expo (E) = (-1,-1)                                            
lowest_expo (Polynomial (c1,expo1,(E))) = (c1,expo1)
lowest_expo (Polynomial (c1,expo1,(Polynomial (c2,expo2,t)))) = if expo1 <expo2 then (lowest_expo (Polynomial (c1,expo1,(t)))) else (lowest_expo (Polynomial (c2,expo2,t)))

discard_my_values end (Polynomial (c1,expo1,(E))) = (E)
discard_my_values low_expo (Polynomial (c,expo,t)) = if low_expo==expo then (t) else (Polynomial (c,expo, (discard_my_values (low_expo) (t))))

order_expo (E) = (E)
order_expo (Polynomial (c,expo,E)) = (Polynomial (c,expo,E))
order_expo (a) = let (its_c,low_expo)= lowest_expo (a)
                 in if (low_expo==(-1)) then E else (Polynomial (its_c, low_expo, (order_expo (discard_my_values (low_expo) (a)))))

-- an extra dummy variable, so as to not crash the GUI
notImpl :: ExprV
notImpl = Leaf $ Variable "Not Implemented"


