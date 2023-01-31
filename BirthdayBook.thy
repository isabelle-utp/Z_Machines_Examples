theory BirthdayBook
  imports "Z_Machines.Z_Machine"
begin

\<comment>\<open>We build a system which records people's birthdays, and is able to issue a reminder when the day comes round\<close>

subsection \<open> Types \<close>

type_synonym name = string
type_synonym date = string

\<comment>\<open>we define the set of all names and the set of all dates\<close>
consts
  NAME :: "name set"
  DATE :: "date set"

subsection \<open> State Space \<close>
\<comment>\<open>2 variables are declared\<close>
zstore BirthdayBook = 
  \<comment>\<open>known is the set of names with birthdays recorded\<close> 
  known :: "\<bbbP> name"
  \<comment>\<open>birthday is a function which, when applied to certain names, gives the birthdays associated with them\<close>
  birthday :: "name \<Zpfun> date"
  where 
  \<comment>\<open>the set known is the same as the domain of the function birthday- i.e., the set of names to which it can be validly applied
  this allows value of know to be derived from value of birthday\<close>
  "dom(birthday) = known"
  "known \<subseteq> NAME" 
  "ran(birthday) \<subseteq> DATE"

\<comment>\<open>This operation is to add a new birthday\<close>
zoperation AddBirthday = 
  over BirthdayBook
  \<comment>\<open>name and date are the two inputs to the operation\<close>
  params name\<in>NAME date\<in>DATE
  \<comment>\<open>precodition-the name to be added must not already be one of those known to the system, since each person can only have one birthday\<close>
  pre "name \<notin> known"
  update "[known\<Zprime> = known \<union> {name}
         , birthday\<Zprime> =  birthday \<oplus> {name \<mapsto> date}
         ]"

lemma AddBirthday_inv: "AddBirthday (n, d) preserves BirthdayBook_inv"
  by zpog_full

\<comment>\<open>This operation is to find the birthday of a person known to the system. the state does not change in this operation, therefore there is no update section\<close>
zoperation FindBirthday =
  over BirthdayBook
  \<comment>\<open>operation takes a name as input and yields the
corresponding birthday as output\<close>
  params name\<in>NAME date\<in>DATE
  \<comment>\<open>precondition is that name is one of the names known to the system; if so, the output date is the value of the birthday function at argument name\<close>
  pre "name \<in> dom birthday"
  where "date = birthday(name)"


lemma FindBirthday_inv: "FindBirthday (n, d) preserves BirthdayBook_inv"
  by zpog_full


\<comment>\<open>this operation is to find which people have
birthdays on a given date\<close>
zoperation Remind =
  over BirthdayBook
  \<comment>\<open>The operation has one input today, and one output cards, which is a set of names: there may be 0, 1, or more people with birthdays on a particular day, to whom birthday cards should be sent\<close>
  params today\<in>DATE cards\<in>"\<bbbP> NAME"
  \<comment>\<open>cards is to be equal to the set of all values n drawn from the set known such that the value of the birthday function at n is today\<close>
  where "cards = {n \<in> known. birthday(n) = today}"

lemma Remind_inv: "Remind (n, d) preserves BirthdayBook_inv"
  by zpog_full

zmachine BirthdayBookSys =
  over BirthdayBook
  \<comment>\<open>init- we must say what state the system is in when it is first started. This is the initial state of the system.The initial state is the set known is empty: in consequence, the function birthday is empty too\<close>
  init "[known \<leadsto> {}, birthday \<leadsto> {\<mapsto>}]"
  invariant BirthdayBook_inv
  operations AddBirthday FindBirthday Remind

definition [z_defs]: "BirthdayBook_axioms = (NAME \<noteq> {} \<and> DATE \<noteq> {})"

thm disjE
thm exE

\<comment>\<open>this lemma is to prove the system is deadlock free. \<close>
lemma BirthdayBook_deadlock_free: "BirthdayBook_axioms \<Longrightarrow> deadlock_free BirthdayBookSys" 
  by (deadlock_free invs: AddBirthday_inv FindBirthday_inv Remind_inv; auto)

def_consts NAME = "{STR ''Simon''}" 
def_consts DATE = "{STR ''25/08/1983''}"

animate BirthdayBookSys

end