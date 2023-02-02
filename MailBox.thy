theory MailBox
  imports "Z_Machines.Z_Machine"
begin

\<comment>\<open>An electronic mail system consists of several instances of the component MailBox. Each instance may be associated with one or more addresses from the set Address. A user of the system may have more than one address, and an address may be associated with more than one user.\<close>

subsection \<open> Types \<close>

type_synonym user = string
type_synonym address = string
type_synonym mailbox = string
type_synonym message = string
type_synonym timestamp = string

\<comment>\<open>we define the set of all users, address, and mialboxes\<close>
consts
  USER :: "user set"
  ADDRESS :: "address set"
  MAILBOX :: "mailbox set"
  MESSAGE ::  "message set"
  TIMESTAMP :: "timestamp set"

subsection \<open> State Space \<close>
\<comment>\<open>3 variables are declared. mail is a sequence of type Message, representing the mail messages stored in the box.
new_mail records the time of arrival of the latest mail message, and last_read records the last time that mail in the box was read.\<close>
zstore MailBox =
  mail :: "message list"
  new_mail :: "timestamp"
  last_read :: "timestamp"


\<comment>\<open>Global: The association between users and addresses is given by a relation address, and the association between addresses and the local mailboxes is given by the partial function mailbox\<close>
zstore MailSystem =
  address :: "user \<leftrightarrow> address"
  mailbox :: "address \<Zpfun> MailBox"
  where "dom(mailbox) = ADDRESS"

subsection \<open> operations \<close>

\<comment>\<open>this local operation describes the effect of adding mail to a single mailbox.
The incoming message is added to the end of the sequence mail, and the new mail is set to t. The other time stamp last_read remains unchanged so omitted.\<close>
zoperation ReceiveBox = 
  over MailBox
  \<comment>\<open>m and t are the two inputs to the operation\<close>
  params m\<in>MESSAGE  t\<in>TIMESTAMP
  update "[mail\<Zprime> = mail @ [m]
         , new_mail\<Zprime> =  t
         ]"

\<comment>\<open>f a message m arrives at time t for user u, then it will be added to one of the mailboxes belonging to u.
a is provided as an output to the operation.
u, m, t are inputs\<close>
zoperation ReceiveSystem = 
  over MailSystem
  params u\<in>USER a\<in>ADDRESS m\<in>MESSAGE  t\<in>TIMESTAMP
  pre "(a\<in> dom mailbox \<and> u \<in> dom address \<and> address(u) = a) "
  update "[mailbox[a]:mail\<Zprime>= $mailbox[a]:mail @ [m]
         , mailbox[a]:new_mail\<Zprime> =  t
         ]"


def_consts USER = "{ ''Carolyn'',  ''Denise'',  ''Edward''}" 

def_consts ADDRESS = "{ ''admin'',  ''carolyn'',  ''denise'',  ''edward'',  ''edwardc''}" 

def_consts TIMESTAMP = "{''Tue 14 Feb, 11:00 a.m.'', ''Thur 16 Feb, 09:00 a.m.'',  ''Tue 12 Mar, 09:50 a.m.'',  ''Mon 18 Mar, 03 p.m.''}" 

def_consts MESSAGE = "{''m1'', ''m2'',  ''m3'',  ''m4'',  ''m5''}" 

zmachine MailSystemProc =
  over MailSystem
  init "[address\<Zprime> = {''Carolyn'' \<mapsto> ''admin'', ''Carolyn'' \<mapsto> ''carolyn'', ''Denise''  \<mapsto> ''denise'', ''Denise''  \<mapsto>''admin'', ''Edward''  \<mapsto>''edward'',  ''Edward''  \<mapsto>''edwardc''},
        mailbox\<Zprime> = {
        ''admin'' \<mapsto>  \<lblot>mail\<leadsto> [],new_mail \<leadsto>'' '', last_read\<leadsto> '' ''  \<rblot>,
        ''carolyn'' \<mapsto>\<lblot>mail\<leadsto> [],new_mail \<leadsto>'' '', last_read\<leadsto> '' ''  \<rblot>,
        ''denise'' \<mapsto> \<lblot>mail\<leadsto> [],new_mail \<leadsto>'' '', last_read\<leadsto> '' ''  \<rblot>,
        ''edward'' \<mapsto> \<lblot>mail\<leadsto> [],new_mail \<leadsto>'' '', last_read\<leadsto> '' ''  \<rblot>,   
        ''edwardc'' \<mapsto>\<lblot>mail\<leadsto> [],new_mail \<leadsto>'' '', last_read\<leadsto> '' ''  \<rblot>}
       ]"
  operations ReceiveSystem


animate MailSystemProc

end