-------------------------- MODULE Channels --------------------------

EXTENDS Integers, Sequences, TLC

Channels(channels) == [ c \in channels |-> <<>> ]

HasMessage(channel, client) == channel[client] /= <<>>

NextMessage(channel, client) == Head(channel[client])

MarkMessageReceived(channel, client) == [channel EXCEPT ![client] = Tail(channel[client])]

SendToChannel(channel, client, msg) == [channel EXCEPT ![client] = Append(channel[client], msg)]

=============================================================================