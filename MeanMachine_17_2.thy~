theory MeanMachine_17_2
  imports "Z_Machines.Z_Machine"
begin 



\<comment>\<open>Usingz ex 17.2: We are required to produce a program that finds the average of some numbers. We decide that the program should find the arithmetic mean of some natural numbers.\<close>

consts N :: "nat set"

fun sumList :: "nat list \<Rightarrow> nat" where
"sumList [] = 0" | 
"sumList (x # xs) = x + sumList xs"


\<comment>\<open>The state of the program is modelled using a sequence of natural numbers to represent the data set\<close>
zstore AMemory =
   s :: "nat list"
\<comment>\<open>The use of a list than a set is important here, as we
may be faced with many copies of the same natural number.\<close>


\<comment>\<open>Our specification describes a simple interface consist-
ing of two operations: an operation AEnter that adds a number to our data set and an operation AMean that calculates the arithmetic mean of the numbers entered thus far.\<close>

\<comment>\<open>As each number is entered, it is added to the end of the list.\<close>
zoperation AEnter =
  over AMemory
  params n \<in> N
  update "[s\<Zprime> = s @[n]]"

consts R ::"real set"


\<comment>\<open>The arithmetic mean of a series is its sum divided by its length. \<close>
zoperation AMean =
  over AMemory
  params m \<in> "{(sumList s) div (length s)}"
  pre "s \<noteq> []"
\<comment>\<open>The result makes sense only if the length of the list is strictly positive: precondition\<close>
\<comment>\<open>m is an output, we constrain its value to a singlton set which only contains its value\<close>


\<comment>\<open>In the initial state, the sequence of numbers is empty.\<close>
definition Init :: "AMemory subst" where
  [z_defs]:
  "Init = 
   [s\<Zprime> =[] 
   ]"

zmachine AMemoryProc = 
  init Init
  invariant AMemory
  operations AEnter AMean

def_consts N = "{0..5}"

animate AMemoryProc


\<comment>\<open>It is not necessary to keep the entire sequence of numbers that has been input; there is another way to compute the mean. 
In a specification we are more concerned with clarity than with efficiency, so the summation over a series is entirely appropriate. 
We will now consider a design in which only two numbers are stored: the running total and the sample size.\<close>

\<comment>\<open>The state comprises two natural numbers.\<close>
zstore CMemory =
   sum :: "nat"
   size:: "nat"

\<comment>\<open>When a number is entered, it is added to the running total, and the sample size is increased by one.\<close>
zoperation CEnter =
  over CMemory
  params n \<in> N
  update "[sum\<Zprime> = sum + n
          ,size\<Zprime> =size + 1]"


\<comment>\<open>If at least one number has been entered, then the mean may be obtained by dividing the running total by the sample size.\<close>
zoperation CMean =
  over CMemory
  params m \<in>  "{ sum div size}"
  pre "size \<noteq> 0 "


\<comment>\<open>In the initial state, both of these are zero.\<close>
definition Init1 :: "CMemory subst" where
  [z_defs]:
  "Init1 = 
   [sum\<Zprime> =0,
    size\<Zprime> = 0 
   ]"

zmachine CMemoryProc = 
  init Init1
  invariant CMemory
  operations CEnter CMean

(*SumSizeRetrieve ? ? ? ?*)

(*theorems  ? ? ? ?*)



animate CMemoryProc

end