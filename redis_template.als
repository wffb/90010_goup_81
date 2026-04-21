// =============================================================================
// SWEN90010 Assignment 2 — Redis/ChatGPT Data Leakage Model
// =============================================================================
//
// Student 1: [BO HUANG, 1584795]
// Student 2: [Name, Student ID]
// Student 2: [Name, Student ID]
//
// =============================================================================

// Debugging: each action predicate records which action was last performed,
// to make it easier to interpret traces produced by Alloy.
// The correspondence between Action values and predicates is:
//   DoNothing           -> do_nothing
//   UserSendReq         -> action_user_send_http_request
//   UserRecvResp        -> action_user_recv_http_response
//   RecvReqAcquireConn  -> action_recv_http_request_and_acquire_connection
//   RedisProcess        -> action_redis_process_connection
//   ReleaseConnSendResp -> action_release_connection_and_send_http_response
//   RequestCancelled    -> action_user_request_cancelled
abstract sig Action {}
one sig DoNothing, UserSendReq, UserRecvResp, RecvReqAcquireConn,
              RedisProcess, ReleaseConnSendResp, RequestCancelled extends Action {}

// Data is the abstract type of all data in the system.
// UserData represents data that belongs to a specific user.
// DataRequestCancelled is a special sentinel value used to inform
// a user that their request was cancelled.
abstract sig Data {}
sig UserData extends Data {}
one sig DataRequestCancelled extends Data {}

// Each User has a set of UserData items that belong to them.
sig User {
  my_data : set UserData
}

// Task 1a: Write a predicate user_data_disjoint that expresses the property
// that no two different users share any data items. Test it, then promote
// it to a fact.

fact user_data_disjoint {
  // For any two distinct users, their my_data sets must not intersect.
  // "u1.my_data & u2.my_data" is the intersection of their data sets.
  // "no X" asserts that set X is empty.
  all u1, u2 : User | u1 != u2 implies no (u1.my_data & u2.my_data)
}

// HTTP messages carry Data as their contents.
// An HTTPRequest is sent by a user (src) to the server.
// An HTTPResponse is sent by the server to a user (dest).
abstract sig HTTPMessage {
  contents : Data
}

sig HTTPResponse extends HTTPMessage {
  dest : User
}

sig HTTPRequest extends HTTPMessage {
  src : User
}

// Connections model the Redis connection pool. Each connection can be
// allocated to at most one user at a time and has separate send/recv
// data buffers for communicating with the Redis backend.
sig Connection {}

// The State records the current state of the entire system.
// http_network: holds at most one HTTP message in transit between users and the server.
// connection_send_data: for each connection, the user data being sent to Redis.
// connection_recv_data: for each connection, the user data received back from Redis.
// connection_for: records which user (if any) each connection is currently allocated to.
// last_action: records the most recent action, for debugging/trace readability.
one sig State {
  var http_network : lone HTTPMessage,
  var connection_send_data : Connection -> lone UserData,
  var connection_recv_data : Connection -> lone UserData,
  var connection_for : Connection -> lone User,
  var last_action : Action
}

// When BugFixed is present, the bug fix is enabled.
// When BugFixed is absent, the system exhibits the vulnerable behaviour.
lone sig BugFixed {}

// Task 1b: Complete the Init predicate.
pred Init {
  // The HTTP network carries no message.
  no State.http_network
  
  // No connection has data in its send buffer.
  no State.connection_send_data
  
  // No connection has data in its receive buffer.
  no State.connection_recv_data
  
  // No connection is allocated to any user.
  no State.connection_for
  
  // The "previous action" is the no-op marker, since nothing has happened yet.
  State.last_action = DoNothing
}

// Task 1c: Complete the action_user_send_http_request predicate.
pred action_user_send_http_request {
  // -------- Preconditions --------
  // The network must be empty before a user can send a new request,
  // because http_network can hold at most one message at a time.
  no State.http_network
  
  // -------- Effect: pick a sender, a piece of their data, and a request --------
  // There exists some user u, some data d owned by u, and some HTTPRequest req
  // such that, after this action, the network carries req with src=u, contents=d.
  some u : User, d : UserData, req : HTTPRequest | {
    // The chosen data must belong to the sending user.
    d in u.my_data
    
    // The request on the wire is tagged as coming from u and carries d.
    req.src = u
    req.contents = d
    
    // In the next state, the network holds this specific request.
    State.http_network' = req
  }
  
  // -------- Frame conditions: other state fields unchanged --------
  State.connection_send_data' = State.connection_send_data
  State.connection_recv_data' = State.connection_recv_data
  State.connection_for'       = State.connection_for
  
  // -------- Bookkeeping --------
  // Record that this was the last action, for trace readability.
  State.last_action' = UserSendReq
}

// Task 1d: Complete the action_user_recv_http_response predicate.
pred action_user_recv_http_response {
  // -------- Preconditions --------
  // The network must currently hold an HTTPResponse. We express this by
  // saying "there exists a response that is on the network". Since the
  // network holds at most one message, this also pins down which message
  // is being received.
  some resp : HTTPResponse | resp in State.http_network
  
  // -------- Effect --------
  // After this action, the network is empty — the message has been taken.
  no State.http_network'
  
  // -------- Frame conditions --------
  State.connection_send_data' = State.connection_send_data
  State.connection_recv_data' = State.connection_recv_data
  State.connection_for'       = State.connection_for
  
  // -------- Bookkeeping --------
  State.last_action' = UserRecvResp
}

// Task 1e: Complete the action_recv_http_request_and_acquire_connection predicate.
pred action_recv_http_request_and_acquire_connection {
      some c : Connection, req : HTTPRequest | {
    // -------- Preconditions --------
    // The request we're processing must actually be on the network.
    req in State.http_network
    
    // The connection we pick must not currently be allocated to any user.
    // State.connection_for[c] is the user that c maps to; "no X" means empty.
    no State.connection_for[c]
    
    // -------- Effects --------
    // The network is emptied: the request has been taken off the wire.
    no State.http_network'
    
    // Record that c is now allocated to the sender of req.
    // "+ (c -> req.src)" adds a single tuple to the relation.
    State.connection_for' = State.connection_for + (c -> req.src)
    
    // Write the request's contents into c's send buffer.
    State.connection_send_data' = State.connection_send_data + (c -> req.contents)
  }
// -------- Frame conditions --------
  // The receive buffer is not touched by this action.
  State.connection_recv_data' = State.connection_recv_data
  
  // -------- Bookkeeping --------
  State.last_action' = RecvReqAcquireConn

}

// Task 1f: Complete user_data_for_same_user and action_redis_process_connection.
pred user_data_for_same_user[d, d2 : UserData] {
  // FILL IN HERE
}

pred action_redis_process_connection {
  // FILL IN HERE
}

// Task 1g: Complete the action_release_connection_and_send_http_response predicate.
pred action_release_connection_and_send_http_response {
  // FILL IN HERE
}

// Task 1h: Complete the action_user_request_cancelled predicate.
pred action_user_request_cancelled {
  // FILL IN HERE
}

// Given: do_nothing predicate (do not modify)
pred do_nothing {
  State.http_network' = State.http_network
  State.connection_for' = State.connection_for
  State.connection_recv_data' = State.connection_recv_data
  State.connection_send_data' = State.connection_send_data
  State.last_action' = DoNothing
}

// Given: Init is the initial state (do not modify)
fact Init_is_Initial {
  Init
}

// Given: transition relation (do not modify)
fact trans {
  always (do_nothing or action_user_request_cancelled or
              action_release_connection_and_send_http_response or
              action_redis_process_connection or
              action_recv_http_request_and_acquire_connection or
              action_user_recv_http_response or
              action_user_send_http_request)
}

// =============================================================================
// Task 2: Discover the Vulnerability
// =============================================================================

// Task 2a: Write your NoDataLeak assertion and check command here.

// FILL IN HERE


// Task 2b: Write your vulnerability run command here, with comments explaining
// the sequence of events and why the vulnerability arises.

// FILL IN HERE


// =============================================================================
// Task 3: Diagnose the Root Cause
// =============================================================================

// Task 3a: Write your inv predicate and check command here.

// FILL IN HERE


// Task 3b: Write a comment explaining (i) which action predicate causes
// the invariant to be violated and what it fails to do, and (ii) how
// the resulting violation enables the data leakage vulnerability.

// FILL IN HERE


// =============================================================================
// Task 4: Fix and Verify
// =============================================================================

// Task 4a: Using your analysis from Task 3, modify the action predicate
// (above) that is the root cause of the vulnerability to fix the problem.
// Use the BugFixed sig as a guard (see the assignment spec for details).
// (No new code goes here — modify the predicate definition above.)

// Task 4b: Write check commands to verify that when some BugFixed,
// NoDataLeak holds and inv is maintained.

// FILL IN HERE


// Task 4c(i): Discuss your choice of bounds for the verification checks
// in Task 4b. What behaviours are covered? What confidence does a
// successful check provide? What are the limitations of bounded verification?

// FILL IN HERE


// Task 4c(ii): Identify at least one simplification or abstraction in this
// model that could mean a real-world vulnerability goes undetected, and
// explain concretely what kind of vulnerability or behaviour it could miss.

// FILL IN HERE


// --------------- test ---------------------

// for 1a
// Sanity check: the model is still satisfiable with the disjointness fact.
// We expect to find an instance where multiple users each have their own data.
run { 
  some u1, u2 : User | u1 != u2 
  some User.my_data  // at least some users have data
} for 3

check { 
  all u1, u2 : User | u1 != u2 implies no (u1.my_data & u2.my_data)
} for 5


//for 1b
run { } for 3 but 1 steps

//for 1c
run { 
  eventually action_user_send_http_request 
} for 5 but 3 steps

//for 1d
run { 
  eventually action_user_recv_http_response 
} for 5 but 8 steps


// for 13
run { 
  eventually action_recv_http_request_and_acquire_connection 
} for 5 but 5 steps
