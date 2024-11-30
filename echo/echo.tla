-------------------------- MODULE echo --------------------------

EXTENDS Integers, Sequences, TLC, Channels


(* --algorithm echo
variables
  i = 0;
  channel = Channels({"A", "B"});

macro send(to, msg) begin
  channel := SendToChannel(channel, to, msg);
end macro;

macro receive(p, buffer) begin
  await HasMessage(channel, p);
  buffer := NextMessage(channel, p);
  channel := MarkMessageReceived(channel, p);
end macro;

process processA = "A"
variable response;
begin
  Iterate:
    while i < 10 do
      Send:
        send("B", "Hello");
      Receive:
        receive("A", response);
      i := i + 1;
    end while;
end process;

process processB = "B"
variable buffer;
begin
  Receive:
    receive("B", buffer);
  Send:
    send("A", buffer);
  if i < 9 then
    goto Receive;
  end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "f15bb2ca" /\ chksum(tla) = "93c3bded")
\* Label Send of process processA at line 11 col 3 changed to Send_
\* Label Receive of process processA at line 15 col 3 changed to Receive_
CONSTANT defaultInitValue
VARIABLES pc, i, channel, response, buffer

vars == << pc, i, channel, response, buffer >>

ProcSet == {"A"} \cup {"B"}

Init == (* Global variables *)
        /\ i = 0
        /\ channel = Channels({"A", "B"})
        (* Process processA *)
        /\ response = defaultInitValue
        (* Process processB *)
        /\ buffer = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "Iterate"
                                        [] self = "B" -> "Receive"]

Iterate == /\ pc["A"] = "Iterate"
           /\ IF i < 10
                 THEN /\ pc' = [pc EXCEPT !["A"] = "Send_"]
                 ELSE /\ pc' = [pc EXCEPT !["A"] = "Done"]
           /\ UNCHANGED << i, channel, response, buffer >>

Send_ == /\ pc["A"] = "Send_"
         /\ channel' = SendToChannel(channel, "B", "Hello")
         /\ pc' = [pc EXCEPT !["A"] = "Receive_"]
         /\ UNCHANGED << i, response, buffer >>

Receive_ == /\ pc["A"] = "Receive_"
            /\ HasMessage(channel, "A")
            /\ response' = NextMessage(channel, "A")
            /\ channel' = MarkMessageReceived(channel, "A")
            /\ i' = i + 1
            /\ pc' = [pc EXCEPT !["A"] = "Iterate"]
            /\ UNCHANGED buffer

processA == Iterate \/ Send_ \/ Receive_

Receive == /\ pc["B"] = "Receive"
           /\ HasMessage(channel, "B")
           /\ buffer' = NextMessage(channel, "B")
           /\ channel' = MarkMessageReceived(channel, "B")
           /\ pc' = [pc EXCEPT !["B"] = "Send"]
           /\ UNCHANGED << i, response >>

Send == /\ pc["B"] = "Send"
        /\ channel' = SendToChannel(channel, "A", buffer)
        /\ IF i < 9
              THEN /\ pc' = [pc EXCEPT !["B"] = "Receive"]
              ELSE /\ pc' = [pc EXCEPT !["B"] = "Done"]
        /\ UNCHANGED << i, response, buffer >>

processB == Receive \/ Send

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == processA \/ processB
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
