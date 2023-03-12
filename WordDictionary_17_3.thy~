section \<open> Word Dictionary \<close>

theory WordDictionary_17_3
  imports "Z_Machines.Z_Machine"
begin

text \<open>UsingZ ex 17.3:We wish to use a dictionary to check the spelling of words. If the word is in the dictionary, then it is considered to be spelt correctly; if not, then it is considered to be spelt incorrectly.\<close>

subsection \<open> Types \<close>

type_synonym word = string

consts
  Word :: "word set" \<comment> \<open>We define the set of word \<close>


subsection \<open> An abstract state space \<close>
text \<open>Abstractly, the dictionary is simply a set of words.\<close>
zstore ADict =
  ad :: "\<bbbP> (word)"


subsection \<open> a concrete State Space \<close>
\<comment>\<open>The task of implementing the dictionary efficiently is a searching problem. One solution is to keep the dictionary in a sorted order, and employ a binary search method.\<close>
zstore CDict1 =
  cd1 :: "word list" 
  where 
    "distinct cd1" "sorted cd1"
\<comment>\<open>The words are kept (without duplicates, i.e. distinct) in a sequence in ascending order (i.e., sorted).\<close>
(*is sorted ascending order?*)


subsection \<open> A 2nd concrete State Space \<close>
text \<open>Alternatively, we could divide the words according to length, and a search would proceed by looking at only those words of the same length as the word we are checking, thus cutting down the search space.\<close>
zstore CDict2 =
  cd2 :: "(word set )list"
  where "\<forall> i\<in>dom cd2. \<forall>w\<in> cd2 ! i. length w = i"
\<comment>\<open>This design starts by introducing a sequence of sets of words, with each of the sets containing only words of a particular length: the first set has words of length 1, the second of length 2, and so on.\<close>
\<comment> \<open>'i\<in> dom cd2' equivalent to 'i < lenght cd2'\<close>

subsection \<open> A 3rd concrete State Space \<close>
text \<open>As a third alternative, suppose that we are more interested in space efficiency. In this case, we might choose to exploit the common prefixes in the dictionary. 
As an example, suppose that our dictionary were rather sparsely filled with the following words: and, ant , bee, can, and cat . Instead of storing all 15 letters, we need store only 11 of them. The data structure that we have in mind is a tree. 
At its root there are three branches, one for a, one for b, and one for c. Below each of these branches, there is another prefix tree.\<close>

type_synonym letter= string

text \<open>the free type of prefix trees is given:\<close>
datatype wordtree = Tree (ofTree: "letter \<Zpfun> wordtree") | TreeNode  (ofTreeNode: "letter \<Zpfun> wordtree")
\<comment>\<open>The use of two injections—Tree and TreeNode—means that we can capture proper prefixes. The injection TreeNode is used to mark a node that contains the end of a word, even if it is a proper prefix of another word\<close>


zstore CDict3 =
  cd3 :: "wordtree set"


text \<open>Each of the three designs—CDict 1 , CDict 2 , and CDict 3 —forms the basis for a correct data refinement of ADict.\<close>

end