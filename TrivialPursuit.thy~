theory TrivialPursuit    
  imports "Z_Machines.Z_Machine"
begin
\<comment>\<open>In the game of Trivial Pursuit TM , the players collect tokens of various colours—red, green, yellow, blue, brown, and pink—the aim being to collect one token of each colour.\<close>

enumtype player = fang | jim | simon

definition "Player = {fang, jim, simon}"

enumtype colour = blue | pink | yellow | brown | green | orange

definition Colour :: "colour set" where
"Colour = {blue, pink, yellow, brown, green, orange}"

\<comment>\<open>each player maintains an individual score modelled using LocalScore\<close>
zstore LocalScore =
  s :: "colour set"

\<comment>\<open>The overall state of play at any point during the game is given by GlobalScore.
a partial function @score associates each player with his/her score @LocalScore\<close>
zstore GlobalScore =
  score :: "player \<Zpfun> LocalScore"

\<comment>\<open>A player is awarded tokens if and when he/she provides correct answers to questions on various subjects; the colour awarded depends upon the choice of subject.
if a repeated colour is awarded, there is no change  in s as s is a type of set\<close>
zoperation AnswerLocal =
  params c \<in> Colour
  update "[s\<Zprime> =  s \<union> {c}]"

(*
zoperation AnswerGlobal = 
  over GlobalScore
  params p\<in>Player 
  promote AnswerLocal with score[p]
*)

\<comment>\<open>If a player p earns a token of colour c, then the effect upon the state of whole play is described using @AnswerGlobal\<close>
\<comment>\<open>the precondition in this operation: If p is indeed part of the current game, the function score is updated to reflect the new score associated with p\<close>
zoperation AnswerGlobal =
  over GlobalScore
  params p\<in>Player c\<in>Colour
  pre "p\<in> dom score "
  update "[score[p]:s\<Zprime> = $score[p]:s \<union> {c}]"


\<comment>\<open>for each player the initial state of token collected is none\<close>
zmachine LocalTP =
  over LocalScore
  init "[s\<Zprime> = {}]"
  operations AnswerLocal



\<comment>\<open>for all players, the initial state of token collected is none\<close>
zmachine GlobalTP =
  over GlobalScore
  init "[score\<Zprime> = { fang \<mapsto> \<lblot> s \<leadsto> {} \<rblot>
                  , jim \<mapsto> \<lblot> s \<leadsto> {} \<rblot>
                  , simon \<mapsto> \<lblot> s \<leadsto> {} \<rblot>}]"
  operations AnswerGlobal

(*
zmachine GlobalTP1=
  over GlobalScore
  init "[score\<Zprime> = {fang \<mapsto> default, jim \<mapsto> default, simon \<mapsto> default}]"
  operations AnswerGlobal
*)
animate GlobalTP

end