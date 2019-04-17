(*
#############################################
#       Fahimeh Ebrahimi Meymand            #
#               cs710107                    #
#       Project 2: Prolog Interpreter       #
############################################# *)

fun empty x = Var x;
(*Substitution Part*)
fun value S ( Var v) = S v
  | value S (Fun (O,args)) = Fun (O, map(value S) args);

fun comp (S, R) v = value S (R v) ;

fun upd (v, t) S = comp (fn w => if w = v then t else Var w, S);



exception non_unifiable and occurs_check and length and unsolvable and nextrule_check;

fun pairup(nil,nil) = nil
  | pairup (a::b,c::d)= (a,c):: (pairup(b,d))
  | pairup(_) = raise length


fun occurs v(Var w) = (v=w)
  | occurs v(Fun(O,args)) =  List.exists(occurs v)args;

(*Unification Part*)
fun unify_prime((t1,t2),S) =
		let
		   val t1_prime= value S t1 and t2_prime = value S t2
		in
		(
                        (*Remove the commects if you want to see the procedure*)
                       (* OutLine ("Inside Unify: ");
                        OutLine ("t1_prime: " ^ PrintTerm t1_prime);
                        OutLine ("t2_prime: " ^ PrintTerm t2_prime^ "\n");*)
			case (t1_prime, t2_prime) of
				 (Var v, Var w)=> if (v=w) then S else upd(v,t2_prime)S
				|(Var v, _) => if occurs v t2 then raise occurs_check else upd(v,t2_prime)S
				|(_,Var w) => if occurs w t1 then raise  occurs_check else upd(w,t1_prime)S
				|(Fun (o1,tlist1),Fun(o2,tlist2))=>
					if o1=o2 then 
						foldr unify_prime S (pairup(tlist1,tlist2))
					else 
						raise non_unifiable
		)
end;

fun unify (t1,t2,S) = 
  unify_prime((t1,t2),S)
  handle length => raise non_unifiable
        | occurs_ckeck => raise non_unifiable;

       
fun rename l (Var(n,_))= Var (n,l)
  | rename l (Fun(f,args)) = Fun (f,map(rename l) args);
  
(*Solver Part*)
fun solve (goals,db) =
	let
		fun solve (goals,rules,S,level) =
			case (goals,rules,S,level) of
			    (nil,_,S,_)=>  S
			  | (_,nil,_,_) => raise unsolvable
			  | (g::goals, Headed(head,tail)::rules,S,level) =>
				let
					val head_prime = rename level(head) and tail_prime = map (rename level) tail
					val S_prime = unify (head_prime,g,S)  
					handle non_unifiable => raise nextrule_check
				in
				(
                                        (*
                                        Remove the comments is you would like to
                                        track the procedure *)

                                        (*
                                        OutLine ("Inside Solve: ");
                                        OutLine ("Head of Rules: "^ PrintTerm head_prime);
                                        OutLine("Head of Goals: "^ PrintTerm g ^ "\n");*)
                                       
                                        solve(tail_prime@goals,db,comp (S_prime,S),level+1)
				)
		end
		handle nextrule_check =>solve(g::goals,rules,S,level)
	in
        (
                solve (goals, db, empty, 1)
        )
end;

(*Used for extracting variable from the goals*)
fun collectVars (v as Var _) = [v]
  | collectVars (Fun (_,args)) =  foldr (op @) [] (map collectVars args);


(*I needed PrintList for debugging, Although PrintTerm worked but I had to define
* PrintList again (copied from Syntax.sml)*)
fun PrintList nil = ""	
  | PrintList (head::tail) =  foldr op^ "" ((PrintTerm head)::(map (fn x => "," ^ (PrintTerm x)) tail))
    and
       PrintTerm (Fun (s,nil)) = s
     | PrintTerm (Fun (s,list))= foldr op^ "" [s, "(", (PrintList list),")"]	
     | PrintTerm (Var (s,0))   = s					        
     | PrintTerm (Var (s,n))   = foldr op^ "" ["_", s, (Int.toString n)];


exception print_NO
fun OutQuery (goals,db) =
	let
		val S = solve (goals,db) handle unsolvable => raise print_NO

		val vars = foldr (op@) [] (map collectVars(goals))
		val values = map (value S)vars;
        in
	(       

                (*Remove comments if you want to see the procedure*)

             (*   OutLine ("Inside OutQuery: ");
                OutLine ("List of Goals: " ^ PrintList (goals));
                OutLine ("varlist: " ^ PrintList (vars));
                OutLine ("valueList: " ^ PrintList (values) ^ "\n");*)
                
                
                OutSol (pairup(vars,values) handle length => [])
	)
end


fun Prolog (x as (Headed (Var _, _))) =
    OutLine ("Illegal clause:  " ^ PrintClause x)
  | Prolog (x as (Headless (Var _ :: _))) =
    OutLine ("Illegal clause:  " ^ PrintClause x)
  | Prolog (Headed (Fun ("init", nil),nil)) = InitDB ()
  | Prolog (x as (Headed _)) = Assert x
  | Prolog (x as Headless y) =
    (OutLine ("query:  " ^ PrintClause x);
     OutQuery (y, !db)
     handle print_NO => OutLine ("\n\nNo Solution Found!")
    )
