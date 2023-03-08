section \<open>PhoenixCinema\<close>
theory PhoenixCinema_17_4
  imports "Z_Machines.Z_Machine"
begin

text\<open>UsingZ ex 17.4:The Phoenix is a cinema whose box office works as follows. A customer may telephone and ask for a ticket. The box office clerk decides if there is an unsold ticket so as to accommodate the request. 
If there is, then a note is made to reserve a ticket for the caller. When the customer arrives, the box office clerk allocates an unsold ticket which identifies the seat.\<close>

subsection \<open> Phoenix \<close>

text \<open>We define a free type as ticket\<close>
type_synonym ticket = nat

text \<open>The Phoenix maintains a pool of tickets, drawn from a given set.\<close>
consts  Ticket :: "ticket set"
def_consts Ticket= "{0..9}"
text \<open>booked is the free type.\<close>
enumtype booked = yes | no
definition [z_defs]: "Booked = {yes, no}"


subsection \<open> State Space \<close>
text \<open>We will concentrate on the activities of a single customer, keeping track not only of the pool of unused tickets, but also of whether or not this customer has booked a ticket.\<close>  
zstore Phoenix = 
  ppool :: "ticket set"
  bkd :: "booked"

subsection \<open> Operations \<close>

text \<open>The booking operation requires that the customer has not already booked, and that there is a ticket to be allocated\<close>
zoperation PBook =
  over Phoenix
  pre "bkd = no  \<and> ppool\<noteq> {}"
  update "[bkd\<Zprime> = yes
          ]"

text \<open>A successful arrival requires that the customer has booked and that a ticket has been left for them.
Afterwards, the record is updated to say that there is no booking, a ticket is allocated, and the pool of tickets is updated accordingly\<close>
zoperation PArrive =
  over Phoenix
  params t\<in> Ticket
  pre "bkd = yes  \<and> ppool\<noteq> {} \<and> t\<in> ppool"
  update "[bkd\<Zprime> = no
          ,ppool\<Zprime> = ppool - {t}]"


definition Init :: "Phoenix subst" where
  [z_defs]:
  "Init = 
   [ppool\<Zprime> = {0..6},
    bkd\<Zprime> = no
   ]"

zmachine PhoenixMachine = 
  init Init
  operations PBook  PArrive

text \<open>animation\<close>
animate PhoenixMachine 



subsection \<open> Apollo \<close>
text \<open>We contrast this procedure with that of the Apollo theatre. 
At the Apollo, a customer may telephone and ask for a ticket. The box office clerk decides if there is an unsold ticket so as to accommodate the request. 
If there is, then one is allocated and put to one side for the caller. When the customer arrives, the clerk presents the allocated ticket which identifies the seat.
The customer cannot tell the difference between the two booking procedures. The point at which the ticket is allocated—and a nondeterministic choice of seat number is made—cannot be detected by the caller.
The transaction appears the same in each case: the customer telephones the box office, arrives at
the place of entertainment, obtains a ticket, and takes the indicated seat.\<close>


text \<open>The state of the Apollo box office contains a pool of ordinary tickets, and a possibly-null ticket\<close>                                  
zstore Apollo = 
  apool :: "ticket set"
  tkt :: "ticket option"
  where "tkt \<noteq> None \<longrightarrow> the tkt \<notin> apool"
\<comment>\<open>In the book  a free type with a constant null is defined as the type of tkt:  datatype   aTicket = null | tikt "ticket". Here, we use option instead. \<close>

text \<open>The booking operation requires that no ticket has already been reserved by the customer, and that the pool is not empty.
Afterwards, a single ticket is removed from the pool and reserved in the state component tkt.\<close>
zoperation ABook =
  over Apollo
  params x \<in> apool \<comment> \<open> We introduce this parameter to model nondeterminism: we don't know which ticket will be booked from apool. \<close>
  pre "tkt = None  \<and> apool\<noteq> {}"
  update "[tkt\<Zprime> = Some x
          , apool\<Zprime> = apool - {x}
          ]"

text \<open>A successful arrival operation requires that the customer has reserved a ticket. This ticket is then issued, and the pool remains unchanged.\<close>
zoperation AArrive =
  over Apollo
  params t\<in> Ticket
  pre "tkt \<noteq>  None \<and> Some t = tkt "
  update "[tkt\<Zprime> = None
       ]"


definition InitA :: "Apollo subst" where
  [z_defs]:
  "InitA = 
   [apool\<Zprime> = {0..6},
    tkt\<Zprime> = None
   ]"


zmachine ApolloMachine = 
  init InitA
  operations ABook  AArrive



animate ApolloMachine

end
