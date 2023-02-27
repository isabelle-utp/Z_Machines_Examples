section \<open> Building Entry System \<close>

theory BuildingEntry_17_1
  imports "Z_Machines.Z_Machine"
begin

\<comment>\<open>Usingz ex 17.1: We model a system that will monitor the access to a building.
The system should keep track of the people who are inside the building, and should forbid entry by more than a specified number of people at any time.\<close>

\<comment>\<open>we define a basic type\<close>
type_synonym staff = nat

consts 
  Staff :: "staff set"
  maxentry :: nat
\<comment>\<open>maxentry is the maximum number of people that may enter the building at any time\<close>

\<comment>\<open>an abstract state space, s is to record the names of those currently inside the building; the state invariant restricts the number of people to be less or equal than maxentry.\<close>
zstore ASystem = 
  s :: "\<bbbP> staff"
  where "s \<in> \<bbbF> Staff" "#s \<le> maxentry"


\<comment>\<open>A person who is not already recorded as being inside the building may enter it, providing there is enough room, i.e., s has not reached the maximum number.\<close>
zoperation AEnterBuilding =
  over ASystem
  params p\<in>Staff
  pre "#s < maxentry \<and> p \<notin> s"
  update "[s\<Zprime> =  s \<union> {p}]"

\<comment>\<open>A person who is in the building may leave it.\<close>
zoperation ALeaveBuilding =
  over ASystem
  params p\<in>Staff
  pre "p \<in> s"
  update "[s\<Zprime> =  s - {p}]"

\<comment>\<open>Initially, there is no-one in the building\<close>
zmachine ABuildingEntry =
  over ASystem
  init "[s\<Zprime> = {}]"
  operations AEnterBuilding ALeaveBuilding



def_consts 
  Staff = "{0..10}"
  maxentry = "5"

animate ABuildingEntry


\<comment>\<open>A more CONCRETE specification might model the state of the system as an injective sequence: a sequence with no repetitions - iseq. The length of this sequence
must be less than maxentry\<close>
zstore CSystem =
  l :: "staff list"
  where 
    "l \<in> iseq Staff" "#l \<le> maxentry"
\<comment>\<open>The length of l represents the number of people inside the building.\<close>

\<comment>\<open>A person who is not already inside the building may enter it, providing there is enough room.\<close>
zoperation CEnterBuilding =
  params p \<in> Staff
  pre "#l < maxentry \<and> p \<notin> ran l"
  update "[l\<Zprime> =  l @ [p]]"

\<comment>\<open>A person who is in the building may leave it.\<close>
zoperation CLeaveBuilding =
  params p \<in> Staff
  pre "#l < maxentry \<and> p \<in> ran l"
  update "[l\<Zprime> =  l\<restriction> (Staff-{p}) ]"

\<comment>\<open>Initially, there is no one in the building\<close>
zmachine CBuildingEntry =
  over CSystem
  init "[l\<Zprime> = []]"
  operations CEnterBuilding CLeaveBuilding


(*what to do with ListRetrieveSet ? ? ? ?*)

term CSystem_inv

definition ListRetrieveSet :: "CSystem \<Rightarrow> (_, ASystem) itree" where
"ListRetrieveSet = \<questiondown>CSystem_inv? ;; \<langle>\<lblot>s \<leadsto> set l\<rblot>\<rangle>\<^sub>a"

definition SetRetrieveList :: "ASystem \<Rightarrow> (_, CSystem) itree" where
"SetRetrieveList = \<questiondown>ASystem_inv? ;; \<langle>\<lblot>l \<leadsto> sorted_list_of_set s\<rblot>\<rangle>\<^sub>a"

find_theorems "(\<circ>\<^sub>s)"

lemma "ListRetrieveSet ;; SetRetrieveList = \<questiondown>CSystem?"
  apply (simp add: ListRetrieveSet_def SetRetrieveList_def ASystem_inv_def assigns_seq kcomp_assoc assigns_assume assigns_seq_comp usubst usubst_eval)

lemma "p \<in> Staff \<Longrightarrow> (ListRetrieveSet ;; AEnterBuilding p) \<sqsubseteq> (CEnterBuilding p ;; ListRetrieveSet)"
  unfolding ListRetrieveSet_def AEnterBuilding_def CEnterBuilding_def
  apply refine_auto
   apply (simp add: distinct_card)
  done
  
end

