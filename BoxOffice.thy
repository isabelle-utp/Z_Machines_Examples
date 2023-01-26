subsection \<open> Theatre Box Office \<close>

theory BoxOffice
  imports "Z_Machines.Z_Machine"
begin

text\<open>A concert hall uses a software system to keep track of bookings for performances. Inside the hall is a certain amount of seating, some or all of which may be made available to customers for a given performance.\<close>

subsection \<open> Types \<close>

text\<open>we define two free type as seat and customer\<close>
type_synonym seat = integer
type_synonym customer = string
type_synonym performance = string

\<comment>\<open>A show may be a standard performance, or it may be a premiere.\<close>
enumtype Status = standard | premiere
definition [z_defs]: "Status = {standard, premiere}"

\<comment>\<open>ex12.8, replace sorry for nope\<close>
enumtype Response = okay | nope
definition [z_defs]: "Response = {okay, nope}"

text\<open>At this level of abstraction, we have no need to consider the representation of seats and customers, so we introduce them as sets\<close>
consts 
  initalloc :: "seat set"
  SEAT      :: "seat set"
  CUSTOMER  :: "customer set"
  PERFORMANCE:: "performance set"

subsection \<open> Functions \<close>
fun free :: "(seat set) \<times> (seat set)  \<Rightarrow> nat"
  where "free(a, b) = #(a - b)"
(*#(a\<setminus>b) does not work: \setminus*)

value "free({1,2,3,4,5,6,7},{2,3})"


subsection \<open> State Space \<close>
  
zstore BoxOffice = 
  \<comment> \<open>seating to represent the seating allocated for the performance. \<close>
  seating :: "seat set"
  \<comment> \<open>  a record of which seats have been sold, and to whom. It is a partial function, that is, no seat can be sold to two different customers, it is a subset of SEAT \<close>
  \<comment>\<open>the order of variables is unimportant\<close>
  sold :: "seat \<Zpfun> customer"

  \<comment> \<open>status: the type of the performance: standard or premier\<close>
  status:: "Status"
  \<comment> \<open> a special type of customers who signed up as friends and are entitled to buy premier performance\<close>
  friends:: "customer set"
  \<comment> \<open> invariant 1: It should not be possible to book seating that has not been allocated for the performance \<close>
 
  \<comment>\<open>announced: a set of performance announed for a box office, these performance can be or not be opened for booking\<close>
 (* For Promotion:
  announced:: "performance set"
  booking:: "performance \<Zpfun> BoxOffice"*)
  where "dom(sold) \<subseteq> seating"
  \<comment> \<open> invariant 2: If the current performance is a premiere, then seats may be sold only to friends of the theatre. \<close>
   "status= premiere \<longrightarrow> ran sold \<subseteq> friends"



subsection \<open> Operations \<close>

\<comment> \<open>Operation 'Purchase0' upon the state of the box office system is the purchasing of a single seat for the current performance by a customer.
this seat is denoted by s;
the customer buying it is c;
If the operation is to be a success, then s must be available for sale beforehand;
Afterwards, the sold relation should be modified to indicate that s has been
sold to customer c;
As seats allocated for this performance are unchanged by the operation, we omit seat in update section.
\<close>
\<comment>\<open>PurchaseSucess = Purchase0 /\ Success\<close>
zoperation PurchaseSuccess =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER
  pre "s \<notin> dom(sold) \<and> s\<in>seating"
  update "[sold \<leadsto> sold \<oplus> {s \<mapsto> c}
         , r\<Zprime>=okay
          ]"
(*\setminus brings error: 
pre "s\<in>seating\<setminus> dom(sold)"*)

\<comment>\<open>ex12.12: PurchaseFailure = NotAvailable /\ Failure\<close>
zoperation PurchaseFailure =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER
  pre "s \<notin> dom(sold) \<and> s\<notin>seating"
  update "[r\<Zprime>=nope
          ]"

\<comment>  \<open> Having purchased a seat, a customer may decide not to attend the performance. In this case, they may return the seat to the box office 
The precondition for this operation is that the seat s has been sold to the customer c.
The effect is defined using domain subtraction \<Zndres> to remove  {s \<mapsto> c} from sold\<close>

\<comment> \<open>ReturnSucess= Return0 \<and> Success\<close>
zoperation ReturnSuccess =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER
  pre "s \<in> dom(sold) \<and> c = sold s"
  update "[sold \<leadsto> {s} \<Zndres> sold
         , r\<Zprime>=okay
           ]" 

\<comment> \<open>ex12.13: ReturnFailure= NotPossible \<and> Failure
If this seat has not been sold, or if it has been sold to another customer, then it can not be returned\<close>
zoperation ReturnFailure =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER r\<in>"{nope}"
  pre " c \<noteq> sold s"
 


\<comment> \<open>shall this be an operation or integrated to other operations?\<close>
zoperation QueryAvailability =
  over BoxOffice
  params available\<in>"{free(seating, dom sold)}"




subsection \<open> Structural Invariants \<close>

lemma PurchaseSuccess_inv[hoare_lemmas]: "PurchaseSuccess(s, c) preserves BoxOffice_inv"
  apply (zpog_full; auto)
  oops

lemma PurchaseFailure_inv[hoare_lemmas]: "PurchaseFailure(s, c) preserves BoxOffice_inv"
  by (zpog_full; auto)


lemma ReturnSuccess_inv[hoare_lemmas]: "ReturnSuccess(s, c) preserves BoxOffice_inv"
  apply (zpog_full; auto)
  oops

lemma ReturnFailure_inv[hoare_lemmas]: " ReturnFailure(s, c) preserves BoxOffice_inv"
  by (zpog_full; auto)


lemma QueryAvailability_inv[hoare_lemmas]: "QueryAvailability() preserves BoxOffice_inv"
  by (zpog_full; auto)


subsection \<open> Safety Requirements \<close>




subsection \<open> Machine and Animation \<close>

zmachine BoxOfficeProc =
  init "[seating \<leadsto> initalloc, sold \<leadsto> {\<mapsto>}]"
  invariant BoxOffice_inv
  operations PurchaseSuccess  PurchaseFailure  ReturnSuccess ReturnFailure QueryAvailability


method deadlock_free uses invs =
  (rule deadlock_free_z_machine
  ,zpog_full
  ,(simp, auto intro!: hl_zop_event hoare_lemmas invs)
  ,(simp add: zop_event_is_event_block extchoice_event_block z_defs z_locale_defs wp Bex_Sum_iff,
    expr_simp add: split_sum_all split_sum_ex))




declare [[show_sorts]]

ML \<open> @{term "case x of Inl x \<Rightarrow> fst (f x) | Inr x \<Rightarrow> fst (g x)" }\<close>

lemma [simp]: "fst (case_sum f g x) = (case x of Inl x \<Rightarrow> fst (f x) | Inr x \<Rightarrow> fst (g x))"
  by (auto simp add: sum.case_eq_if)


ML \<open> @{term "case x of Inl (x::'c) \<Rightarrow> fst (f x) | Inr (x::'d + 'e) \<Rightarrow> fst (case x of Inl (x::'d) \<Rightarrow> g x)"}\<close>

lemma [simp]: "fst (if b then x else y) = (if b then (fst x) else (fst y))"
  by (simp add: if_distrib)



lemma sum_explode: "(\<forall> x :: unit + 'a . P x) \<longleftrightarrow> (P (Inl ()) \<and> (\<forall> y::'a. P (Inr y)))"
  by (auto simp add: sum.case_eq_if, metis old.sum.inducts old.unit.exhaust)

definition [z_defs]: "BoxOffice_axioms = (SEAT \<noteq> {} \<and> CUSTOMER \<noteq> {})"

lemma BoxOfficeProc_deadlock_free: "BoxOffice_axioms \<Longrightarrow> deadlock_free BoxOfficeProc" 
  unfolding BoxOfficeProc_def
  apply deadlock_free
  oops






subsection \<open> We define finite sets for each of the given sets to allow animation. \<close>

def_consts 
  initalloc = "SEAT"
  SEAT = "{0,1,2,3}"
  CUSTOMER = "{STR ''Simon'', STR ''Jim'', STR ''Christian''}"

animate BoxOfficeProc

end