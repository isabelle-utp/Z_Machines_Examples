section \<open> Resource Manager \<close>

theory ResourceManager
  imports "Z_Machines.Z_Machine"
begin 

type_synonym resource = int
consts Resource :: "resource set"

\<comment>\<open>A resource manager allocates identical but numbered resources to client programs or users.
Using a set of numbers @free to describe the free resources\<close>

zstore ResourceManager =
   free :: "resource set"

\<comment>\<open>Any resource that is currently free may be allocated.If there is more than one resource free, then this specification is nondeterministic.\<close>
zoperation Allocate =
  over ResourceManager
  params r \<in> Resource
  pre "r \<in> free"
  update "[free\<Zprime> = free - {r}]"

\<comment>\<open>a refined version of Allocate: should there be more than one resource free, the resource with the lowest number should be allocated first. \<close>
zoperation Allocate1 =
  over ResourceManager
  params r \<in> Resource
  pre "r \<in> free \<and> r = Min free "
  update "[free\<Zprime> = free - {r}]"
(* free\<noteq>{} is not necessary in precondition as 'r \<in> free' implies it
   but for animation, 'r \<in> free' must be before 'r = Min free'*)

zoperation Deallocate =
  over ResourceManager
  params r \<in> Resource
  pre "r \<notin> free"
  update "[free\<Zprime> = free \<union> {r}]"

lemma Allocate\<^sub>1_refines_Allocate: "Allocate r \<sqsubseteq>\<^sub>\<D> Allocate1 r"
  unfolding Allocate_def Allocate1_def oops



zmachine ResourceManagerProc =
  over ResourceManager
  init "[ free\<Zprime> = {0..5}]"
  operations Allocate1  Deallocate

def_consts Resource = "{0..5}"


animate ResourceManagerProc

end