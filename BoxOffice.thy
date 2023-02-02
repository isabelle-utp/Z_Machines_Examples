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


enumtype Response = okay | "sorry"
definition [z_defs]: "Response = {okay, sorry}"

text\<open>At this level of abstraction, we have no need to consider the representation of seats and customers, so we introduce them as sets\<close>
consts 
  initalloc :: "seat set"
  SEAT      :: "seat set"
  CUSTOMER  :: "customer set"
  PERFORMANCE:: "performance set"


subsection \<open> Functions \<close>
fun free :: "(seat set) \<times> (seat set)  \<Rightarrow> nat"
  where "free(a, b) = #(a - b)"


subsection \<open> State Space \<close>
  
zstore BoxOffice = 
  \<comment> \<open>seating to represent the seating allocated for the performance, it is a subset of SEAT.\<close>
  seating :: "seat set"
  \<comment> \<open>  a record of which seats have been sold, and to whom. It is a partial function, that is, no seat can be sold to two different customers \<close>
  sold :: "seat \<Zpfun> customer"
  \<comment> \<open>status: the type of the performance: standard or premier\<close>
  status:: "Status"
  \<comment> \<open> a special type of customers who signed up as friends and are entitled to buy premier performance\<close>
  friends:: "customer set"
where 
  \<comment> \<open> invariant 1: It should not be possible to book seating that has not been allocated for the performance \<close>
  "dom(sold) \<subseteq> seating"
 (* \<comment> \<open> invariant 2: If the current performance is a premiere, then seats may be sold only to friends of the theatre. \<close>
   "status= premiere \<longrightarrow> ran sold \<subseteq> friends"
*)

zstore GlobalOffice = 
  \<comment>\<open>announced: a set of performance announed for a box office, any performance for which we are booking must have been announced.these performance can be or not yet be opened for booking\<close>
  announced:: "performance set"
  booking:: "performance \<Zpfun> BoxOffice"
  where"dom booking \<subseteq> announced"


subsection \<open> Operations \<close>

\<comment> \<open>Operation 'Purchase0' upon the state of the box office system is the purchasing of a single seat for the current performance by a customer.
this seat is denoted by s;
the customer buying it is c;
If the operation is to be a success, then s must be available for sale beforehand;
Afterwards, the sold relation should be modified to indicate that s has been
sold to customer c;
As seats allocated for this performance are unchanged by the operation, we omit seat in update section.
\<close>
\<comment>\<open>PurchaseSucess = Purchase0 /\ Success, 
input s and c, and output r as okay\<close>
zoperation PurchaseSuccess =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER r\<in>"{okay}"
  pre " s\<in>(seating-dom(sold))"
  update "[sold\<Zprime> =  sold \<oplus> {s \<mapsto> c}
          ]"

\<comment>\<open>ex13.4\<close>
zoperation GlobalPurchaseSucess = 
  over GlobalOffice
  params p\<in> PERFORMANCE  s\<in>SEAT c\<in>CUSTOMER r\<in>"{okay}"
  pre "p \<in> dom booking \<and> s\<in>($booking[p]:seating-dom($booking[p]:sold)) "
  update "[booking[p]:sold\<Zprime> = $booking[p]:sold \<oplus> {s \<mapsto> c}]"

\<comment>\<open>ex12.12: PurchaseFailure = NotAvailable /\ Failure\<close>
zoperation PurchaseFailure =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER r\<in>"{sorry}"
  pre "s \<notin> (seating-dom(sold))"

\<comment>\<open>ex13.4\<close>
zoperation GlobalPurchaseFailure =
  over GlobalOffice
  params p\<in> PERFORMANCE s\<in>SEAT c\<in>CUSTOMER r\<in>"{sorry}"
  pre "p \<notin> dom booking \<or> s \<notin> ($booking[p]:seating-dom($booking[p]:sold))"
(*ex13.4 pre: p \<in> dom booking \<and> *)


\<comment>  \<open> Having purchased a seat, a customer may decide not to attend the performance. In this case, they may return the seat to the box office 
The precondition for this operation is that the seat s has been sold to the customer c.
The effect is defined using domain subtraction \<Zndres> to remove  {s \<mapsto> c} from sold\<close>

\<comment> \<open>ReturnSucess= Return0 \<and> Success\<close>

zoperation ReturnSuccess =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER r\<in>"{okay}"
  pre "s \<in> dom(sold) \<and> c = sold s"
  update "[sold\<Zprime> = {s} \<Zndres> sold
           ]" 


zoperation GlobalReturnSuccess =
  over GlobalOffice
  params p\<in> PERFORMANCE s\<in>SEAT c\<in>CUSTOMER r\<in>"{okay}"
  pre "p \<in> dom booking \<and> s \<in> dom($booking[p]:sold) \<and> c = ($booking[p]:sold) s"
  update "[booking[p]:sold\<Zprime> = {s} \<Zndres> $booking[p]:sold 
           ]" 

\<comment> \<open>ex12.13: ReturnFailure= NotPossible \<and> Failure
If this seat has not been sold, or if it has been sold to another customer, then it can not be returned\<close>
zoperation ReturnFailure =
  over BoxOffice
  params s\<in>SEAT c\<in>CUSTOMER r\<in>"{sorry}"
  pre "( s \<in> dom(sold) \<and> c \<noteq> sold s) \<or> s\<notin>dom(sold) "
\<comment>\<open>in pre: 's \<in> dom(sold)' is needed for 'c \<noteq> sold s', otherwise animator has error called at ./Partial_Fun.hs:59:10 in main:Partial_Fun. the reason is that s may be outside of dom sold \<close> 


zoperation GlobalReturnFailure =
  over GlobalOffice
  params p\<in> PERFORMANCE s\<in>SEAT c\<in>CUSTOMER r\<in>"{sorry}"
  pre "p\<notin> dom booking \<or> (s \<in> dom($booking[p]:sold) \<and>  c \<noteq> ($booking[p]:sold) s) \<or> s \<notin> dom($booking[p]:sold)"
 (*do we need pre: s \<in> dom($booking[p]:sold) \<and>  ?*)

\<comment> \<open>ex 12.10: output variables as params \<close>
zoperation QueryAvailability =
  over BoxOffice
  params available\<in>"{free(seating, dom sold)}"

\<comment> \<open> this operation shows the free tickets of one performance.
p is input,available is output.  \<close>
zoperation GlobalQueryAvailability =
  over GlobalOffice
  params p\<in>PERFORMANCE available \<in>"{0..<card(SEAT)+1}"
  pre "available = free($booking[p]:seating, dom ($booking[p]:sold))"
\<comment>\<open>as we can not invoke the parameter within the params section, we describe the relation between available and p in pre section\<close>

subsection \<open> Structural Invariants \<close>

lemma PurchaseSuccess_inv[hoare_lemmas]: "PurchaseSuccess(s, c, r) preserves BoxOffice_inv"
  by (zpog_full)


lemma GlobalPurchaseSucess_inv[hoare_lemmas]: "GlobalPurchaseSucess(p, s, c, r) preserves GlobalOffice_inv"
  by (zpog_full; auto)


lemma PurchaseFailure_inv[hoare_lemmas]: "PurchaseFailure(s, c, r) preserves BoxOffice_inv"
  by (zpog_full; auto)

lemma GlobalPurchaseFailure_inv[hoare_lemmas]: "GlobalPurchaseFailure(s, c, r) preserves GlobalOffice_inv"
  by (zpog_full; auto)


lemma ReturnSuccess_inv[hoare_lemmas]: "ReturnSuccess(s, c, r) preserves BoxOffice_inv"
  by (zpog_full; auto)

lemma GlobalReturnSuccess_inv[hoare_lemmas]: "GlobalReturnSuccess(s, c, r) preserves GlobalOffice_inv"
  by (zpog_full; auto)
  

lemma ReturnFailure_inv[hoare_lemmas]: " ReturnFailure(s, c, r) preserves BoxOffice_inv"
  by (zpog_full; auto)

lemma GlobalReturnFailure_inv[hoare_lemmas]: " GlobalReturnFailure(s, c, r) preserves GlobalOffice_inv"
  by (zpog_full; auto)


lemma QueryAvailability_inv[hoare_lemmas]: "QueryAvailability(a) preserves BoxOffice_inv"
  by (zpog_full; auto)

lemma GlobalQueryAvailability_inv[hoare_lemmas]: "GlobalQueryAvailability(a) preserves GlobalOffice_inv"
  by (zpog_full; auto)


subsection \<open> Safety Requirements \<close>




subsection \<open> Machine and Animation \<close>
def_consts 
  initalloc = "SEAT"
  SEAT = "{0,1,2,3}"
  CUSTOMER = "{ ''Simon'',  ''Jim'',  ''Christian''}"
  PERFORMANCE= "{ ''p1'',  ''p2'', ''p3''}"

zmachine BoxOfficeProc =
  init "[seating\<Zprime> = initalloc, sold\<Zprime>= {\<mapsto>}]"
  operations PurchaseSuccess  PurchaseFailure ReturnSuccess ReturnFailure QueryAvailability

zmachine GlobalBoxOfficeProc =
  init "[booking\<Zprime>={''p1'' \<mapsto> \<lblot> sold \<leadsto> {\<mapsto>} \<rblot>
                  ,''p2'' \<mapsto> \<lblot> sold \<leadsto> {\<mapsto>} \<rblot>
                  ,''p3'' \<mapsto> \<lblot> sold \<leadsto> {\<mapsto>} \<rblot>}]"
  operations 
 GlobalPurchaseFailure  GlobalReturnSuccess  GlobalReturnFailure GlobalQueryAvailability  


subsection \<open> We define finite sets for each of the given sets to allow animation. \<close>


animate GlobalBoxOfficeProc

end
