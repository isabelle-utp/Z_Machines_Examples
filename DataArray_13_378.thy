theory DataArray_13_378
  imports "Z_Machines.Z_Machine"
begin

\<comment>\<open>Usingz ex 13_378\<close>

subsection \<open> Types \<close>

type_synonym "value" = int
\<comment>\<open>value is a keyword, thus quoted\<close>

\<comment>\<open>In a model of a data array, each element may be represented by an object of Data. 
Different from the example in usingz, 
we define Data as a basic type instead of a local state.\<close>
type_synonym Data = "value"


\<comment>\<open>we define the set of values\<close>
consts
  Value :: "value set"
  
subsection \<open> State Space \<close>


\<comment>\<open>Array is Global state in UsingZ, we define it as a local zstore.
The state of the array is represented  with a single component, a sequence of Data elements \<close> 
zstore Array =
  array :: "Data list"

consts Indices :: "nat set"

term list_collection_lens

term "array[0] := undefined"

definition "arr = (array :: Data list \<Longrightarrow> Array)"


term "($arr[0::nat])\<^sub>e"

\<comment>\<open>Operation\<close>
zoperation ArrayAssignData =
  over Array
  params index\<in>Indices  new\<in>Value
  pre "index< length array"
\<comment>\<open>index is the index of array
in Z : index \<in> dom array, 
in ZM we map it to : index < lenght array.\<close>
  update "[array[index]\<Zprime> =new]"


zmachine ArrayProc= 
 over Array
 init "[array\<Zprime> = [1,2,3,4,5]]"
 operations ArrayAssignData

def_consts Indices = "{0..4}"
def_consts Value = "{0..7}"

(*animate ArrayProc*)

record PriData = 
  priority:: "nat"
  data :: "Data"
\<comment>\<open>We convert PriData from a local state in the book 
to a record.\<close>

consts PriDataSet :: "PriData set"


\<comment>\<open>a new state space\<close>
\<comment>\<open>we model a stack of data objects, each of which contains a piece of data and a priority value\<close>
zstore Stack =
  stack ::"PriData list"
  where "\<forall> i< length(stack). \<forall>j< length(stack). i<j \<longrightarrow> priority(stack ! i) \<ge> priority(stack ! j)"
\<comment>\<open>The objects in the stack are ordered with respect to their priority values. 
If object a has a lower index than object b(i.e.,if it is nearer the top of the stack), then it must have a higher priority value\<close>



\<comment>\<open>At any time, only the data object with the highest priority may be operated upon:
that is, the object at the head of the stack.

A new value is added to the top of the stack, its priority is assigned as the value of the previous biggest value plus 1\<close>
zoperation StackAssignPriData =
  over Stack
  params new \<in> Value
  pre "stack \<noteq> []"
  update "[stack\<Zprime> = \<lparr> priority = priority (hd stack) + 1, data = new \<rparr> # stack ]"
(* stack is a record list, we can NOT SEPERATELY update stack by updating 2 fields of data and priority , as they are not state variables.  *)


zoperation Shine = 
  over Stack
  params stk\<in>"{stack}" 


zmachine StackProc= 
 over Stack
 init "[stack\<Zprime> = [\<lparr> priority = 2, data = 0 \<rparr>, \<lparr> priority =1, data = 3 \<rparr>, \<lparr> priority = 0, data = 5 \<rparr>]]"
 operations StackAssignPriData Shine

animate StackProc
end
