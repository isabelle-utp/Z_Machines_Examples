section \<open> Resource Manager \<close>

theory ResourceManager
  imports "Z_Machines.Z_Machine"
begin 

type_synonym resource = integer
consts Resource :: "resource set"

\<comment>\<open>A resource manager allocates identical but numbered resources to client programs or users.
Using a set of numbers @free to describe the free resources\<close>

zstore ResourceManager =
   free :: "resource set"

 (*  
  free :: "integer set"
  res  :: "integer set"
  where "free \<subseteq> res" "res \<subseteq> RES"
  why is res needed? ? ? 
*)

\<comment>\<open>Any resource that is currently free may be allocated.If there is more than one resource free, then this specification is nondeterministic.\<close>
zoperation Allocate =
  over ResourceManager
  params r \<in> Resource
  pre "r \<in> free"
  update "[free\<Zprime> = free - {r}]"

\<comment>\<open>a refined version of Allocate: should there be more than one resource free, the resource with the lowest number should be allocated first. \<close>
zoperation Allocate\<^sub>1 =
  over ResourceManager
  params r \<in> Resource
  pre "r \<in> free \<and> r = Min free \<and> free\<noteq>{}"
  update "[free\<Zprime> = free - {r}]"
(*is free\<noteq>{} necessary? ? ? *)

zoperation Deallocate =
  over ResourceManager
  params r \<in> Resource
  pre "r \<notin> free"
  update "[free\<Zprime> = free \<union> {r}]"

lemma Allocate\<^sub>1_refines_Allocate: "Allocate r \<sqsubseteq> Allocate\<^sub>1 r"
  unfolding Allocate_def Allocate\<^sub>1_def by refine
(*data refinement proof ? ? ?*)


zmachine ResourceManagerProc =
  over ResourceManager
  init "[ free\<Zprime> = {}]"
  operations Allocate\<^sub>1  Deallocate

def_consts Resource = "{0,1,2,3,4,5}"
(*
def_consts Resource = "set (map integer_of_int [0..5])"*)

animate ResourceManagerProc

end