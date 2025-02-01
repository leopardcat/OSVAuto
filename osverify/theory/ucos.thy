imports basic

// Pointer values: each pointer is either null or an address
typedef address = int32u;
enum addrval =
    Vnull
  | Vptr(address addr)

/********************
 * Low level state  *
 ********************/

// Low-level task control block
struct TCB {
    addrval OSTCBEventPtr;      // pointer to event control block
    addrval OSTCBMsg;           // received message
    int16u OSTCBDly;            // time delay
    int16u OSTCBStat;           // task status
    int8u OSTCBPrio;            // priority (0..63)
    int8u OSTCBX;               // bit position in group (0..7)
    int8u OSTCBY;               // index into ready table
    int8u OSTCBBitX;            // bit mask in ready table
    int8u OSTCBBitY;            // bit mask in ready group
}

// Constants for low-level task status
const int16u OS_STAT_RDY = 0;
const int16u OS_STAT_SEM = 1;
const int16u OS_STAT_MBOX = 2;
const int16u OS_STAT_Q = 4;
const int16u OS_STAT_SUSPEND = 8;
const int16u OS_STAT_MUTEX = 16;

// Lowest priority (idle priority)
const int8u OS_LOWEST_PRIO = 63;
const int8u OS_IDLE_PRIO = 63;

// Low-level queue data
struct OS_Q {
    int OSQIn;           // input position
    int OSQOut;          // output position
    int OSQEntries;      // current number of entries in the queue
    Seq<addrval> OSQData;   // list of messages in the queue
}

// Constants for low-level event type
const int8u OS_EVENT_TYPE_UNUSED = 0;
const int8u OS_EVENT_TYPE_MBOX = 1;
const int8u OS_EVENT_TYPE_Q = 2;
const int8u OS_EVENT_TYPE_SEM = 3;
const int8u OS_EVENT_TYPE_MUTEX = 4;

// Low-level event control block
struct EVENT {
    int8u OSEventType;          // type of event control block, one of OS_EVENT_TYPE_UNUSED, etc.
    int8u OSEventGrp;           // ready group of tasks waiting for event
    int16u OSEventCnt;          // semaphore count (for semaphore) or mutex priority (for mutex)
    addrval OSEventPtr;         // pointer to message (for mailbox)
    Seq<int8u> OSEventTbl;      // ready table of tasks waiting for event (size 8)
    Option<OS_Q> OSQueue;       // queue data
}

// Tables used in computations concerning priority table
const Seq<int8u> OSMapTbl = [
    1, 2, 4, 8, 16, 32, 64, 128
];

const Seq<int8u> OSUnMapTbl = [
    0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0x00 to 0x0F                             */
    4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0x10 to 0x1F                             */
    5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0x20 to 0x2F                             */
    4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0x30 to 0x3F                             */
    6, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0x40 to 0x4F                             */
    4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0x50 to 0x5F                             */
    5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0x60 to 0x6F                             */
    4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0x70 to 0x7F                             */
    7, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0x80 to 0x8F                             */
    4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0x90 to 0x9F                             */
    5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0xA0 to 0xAF                             */
    4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0xB0 to 0xBF                             */
    6, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0xC0 to 0xCF                             */
    4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0xD0 to 0xDF                             */
    5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,       /* 0xE0 to 0xEF                             */
    4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0        /* 0xF0 to 0xFF                             */
];

// Low-level global state
struct Global {

    // Task control blocks
    Map<int8u, TCB> OSTCBPrioTbl;       // map priority to TCB pointer

    // Priority map
    int8u OSRdyGrp [binary];        // ready list group
    Seq<int8u> OSRdyTbl;            // table of tasks which are ready to run

    // Map of events
    Map<address, EVENT> events;

    // Time counter
    int32u OSTime;                  // current time

    // Current and highest-priority running tasks
    int8u OSPrioCur;                // priority of current running task
    int8u OSPrioHighRdy;            // priority of highest-priority ready task
}

/********************
 * High level state *
 ********************/

// High-level task status
enum tcbstats =
    os_stat_sem (address ev)
  | os_stat_q (address ev)
  | os_stat_time
  | os_stat_mbox (address ev)
  | os_stat_mutexsem (address ev)

enum taskstatus =
    rdy | wait(tcbstats stat, int16u time)

// High-level task control block
struct AbsTCB {
    int8u prio;
    taskstatus stat;
    addrval msg;
    bool sus;
}

/*
 * Abstract event data
 *
 * For semaphore, specifies semaphore count.
 * For message queue, specifies list of messages and maximum size of the queue,
 * For mailbox, address to the message.
 * For mutex, priority inheritance priority (pip) of the mutex, original priority
 *            of owner, and whether the mutex is owned.
 */
enum eventdata =
    abssem(int16u count)
  | absmsgq(Seq<addrval> msgl, int qsize)
  | absmbox(addrval msg)
  | absmutexsem(int16u prio, int16u oprio, bool owned)

/*
 * Abstract event control block
 *
 * Specifies event information, and list of tasks waiting for the event.
 */
struct AbsECB {
    eventdata edata;
    Seq<int8u> wset;
}

// High-level global state
struct AbsGlobal {
    Map<int8u, AbsTCB> tcbMap;      // address to task control block
    Map<address, AbsECB> ecbMap;    // address to event control block
    int32u curTime;                 // current time
    int8u curTask;                  // current running task
}

/************************
 * Low-level invariants *
 ************************/

// Constraint on the low-level task control block
predicate RL_TCBblk_P (TCB tcb) {
    0 <= tcb.OSTCBPrio && tcb.OSTCBPrio < 64 &&
    tcb.OSTCBPrio & 7 == tcb.OSTCBX &&
    tcb.OSTCBPrio >> 3 == tcb.OSTCBY &&
    1 << tcb.OSTCBX == tcb.OSTCBBitX &&
    1 << tcb.OSTCBY == tcb.OSTCBBitY &&
    (tcb.OSTCBStat == OS_STAT_RDY ||
     tcb.OSTCBStat == OS_STAT_SUSPEND ||
     tcb.OSTCBStat == OS_STAT_SEM ||
     tcb.OSTCBStat == OS_STAT_Q ||
     tcb.OSTCBStat == OS_STAT_MBOX ||
     tcb.OSTCBStat == OS_STAT_MUTEX ||
     tcb.OSTCBStat == OS_STAT_SEM | OS_STAT_SUSPEND ||
     tcb.OSTCBStat == OS_STAT_Q | OS_STAT_SUSPEND ||
     tcb.OSTCBStat == OS_STAT_MBOX | OS_STAT_SUSPEND ||
     tcb.OSTCBStat == OS_STAT_MUTEX | OS_STAT_SUSPEND) &&
    ((tcb.OSTCBStat == OS_STAT_RDY || tcb.OSTCBStat == OS_STAT_SUSPEND) ->
     tcb.OSTCBEventPtr == Vnull)
}

// Whether a priority exists in OSRdyTbl
predicate prio_in_tbl(int8u prio, Seq<int8u> rtbl) {
    let x = prio & 7 in
        rtbl[int(prio >> 3)] & (1 << x) == 1 << x
    end
}

predicate prio_not_in_tbl(int8u prio, Seq<int8u> rtbl) {
    let x = prio & 7 in
        rtbl[int(prio >> 3)] & (1 << x) == 0
    end
}

/**
 * Refinement relation between low-level and high-level task information
 */

// ready case
predicate RLH_RdyI_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    prio_in_tbl(tcb.OSTCBPrio, rtbl) ->
    tcb.OSTCBStat == OS_STAT_RDY && tcb.OSTCBDly == 0 &&
    abstcb.prio == tcb.OSTCBPrio && abstcb.stat == rdy && abstcb.sus == false
}

predicate RHL_RdyI_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    abstcb.stat == rdy && abstcb.sus == false ->
    prio_in_tbl(tcb.OSTCBPrio, rtbl) && tcb.OSTCBPrio == abstcb.prio &&
    tcb.OSTCBStat == OS_STAT_RDY && tcb.OSTCBDly == 0
}

// wait case
predicate RLH_Wait_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBStat == OS_STAT_RDY ->
    tcb.OSTCBDly > 0 && abstcb.prio == tcb.OSTCBPrio &&
    abstcb.stat == wait(os_stat_time, tcb.OSTCBDly) && abstcb.sus == false
}

predicate RHL_Wait_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_time, d), sus: false}}:
            prio == tcb.OSTCBPrio && prio_not_in_tbl(prio, rtbl) &&
            d == tcb.OSTCBDly && d > 0 && tcb.OSTCBStat == OS_STAT_RDY;
        default: true;
    }
}

// suspend case
predicate RLH_Suspend_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    (
        prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBDly == 0 ->
        tcb.OSTCBStat == OS_STAT_SUSPEND ->
        abstcb.prio == tcb.OSTCBPrio && abstcb.stat == rdy && abstcb.sus == true
    )
    &&
    (
        prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBDly > 0 ->
        tcb.OSTCBStat == OS_STAT_SUSPEND ->
        abstcb.prio == tcb.OSTCBPrio && abstcb.stat == wait(os_stat_time, tcb.OSTCBDly) &&
        abstcb.sus == true
    )
}

predicate RHL_Suspend_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    (
        abstcb.stat == rdy -> abstcb.sus == true ->
        prio_not_in_tbl(tcb.OSTCBPrio, rtbl) && tcb.OSTCBPrio == abstcb.prio &&
        tcb.OSTCBDly == 0 && tcb.OSTCBStat == OS_STAT_SUSPEND
    )
    &&
    (
        switch (abstcb) {
            case AbsTCB{{prio: prio, stat: wait(os_stat_time, d), sus: true}}:
                prio == tcb.OSTCBPrio && prio_not_in_tbl(prio, rtbl) &&
                d == tcb.OSTCBDly && d > 0 && tcb.OSTCBStat == OS_STAT_SUSPEND;
            default: true;
        }
    )
}

// semaphore case
predicate RLH_WaitS_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBStat == OS_STAT_SEM ->
    switch (tcb.OSTCBEventPtr) {
        case Vptr(eid):
            abstcb.prio == tcb.OSTCBPrio &&
            abstcb.stat == wait(os_stat_sem(eid), tcb.OSTCBDly) &&
            abstcb.sus == false;
        default: true;
    }
}

predicate RHL_WaitS_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_sem(eid), dly), sus: false}}:
            tcb.OSTCBPrio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.OSTCBEventPtr == Vptr(eid) && tcb.OSTCBStat == OS_STAT_SEM;
        default: true;
    }
}

predicate RLH_WaitS_Suspend_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBStat == OS_STAT_SEM | OS_STAT_SUSPEND ->
    switch (tcb.OSTCBEventPtr) {
        case Vptr(eid):
            abstcb.prio == tcb.OSTCBPrio &&
            abstcb.stat == wait(os_stat_sem(eid), tcb.OSTCBDly) &&
            abstcb.sus == true;
        default: true;
    }
}

predicate RHL_WaitS_Suspend_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_sem(eid), dly), sus: true}}:
            tcb.OSTCBPrio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.OSTCBEventPtr == Vptr(eid) && tcb.OSTCBStat == OS_STAT_SEM | OS_STAT_SUSPEND;
        default: true;
    }
}

// queue case
predicate RLH_WaitQ_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBStat == OS_STAT_Q ->
    switch (tcb.OSTCBEventPtr) {
        case Vptr(eid):
            abstcb.prio == tcb.OSTCBPrio &&
            abstcb.stat == wait(os_stat_q(eid), tcb.OSTCBDly) &&
            abstcb.sus == false;
        default: true;
    }
}

predicate RHL_WaitQ_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_q(eid), dly), sus: false}}:
            tcb.OSTCBPrio == prio && prio_not_in_tbl(prio, rtbl) && 
            tcb.OSTCBEventPtr == Vptr(eid) && tcb.OSTCBStat == OS_STAT_Q;
        default: true;
    }
}

predicate RLH_WaitQ_Suspend_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBStat == OS_STAT_Q | OS_STAT_SUSPEND ->
    switch (tcb.OSTCBEventPtr) {
        case Vptr(eid):
            abstcb.prio == tcb.OSTCBPrio &&
            abstcb.stat == wait(os_stat_q(eid), tcb.OSTCBDly) &&
            abstcb.sus == true;
        default: true;
    }
}

predicate RHL_WaitQ_Suspend_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_q(eid), dly), sus: true}}:
            tcb.OSTCBPrio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.OSTCBEventPtr == Vptr(eid) && tcb.OSTCBStat == OS_STAT_Q | OS_STAT_SUSPEND;
        default: true;
    }
}

// mailbox case
predicate RLH_WaitMB_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBStat == OS_STAT_MBOX ->
    switch (tcb.OSTCBEventPtr) {
        case Vptr(eid):
            abstcb.prio == tcb.OSTCBPrio &&
            abstcb.stat == wait(os_stat_mbox(eid), tcb.OSTCBDly) &&
            abstcb.sus == false;
        default: true;
    }
}

predicate RHL_WaitMB_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_mbox(eid), dly), sus: false}}:
            tcb.OSTCBPrio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.OSTCBEventPtr == Vptr(eid) && tcb.OSTCBStat == OS_STAT_MBOX;
        default: true;
    }
}

predicate RLH_WaitMB_Suspend_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBStat == OS_STAT_MBOX | OS_STAT_SUSPEND ->
    switch (tcb.OSTCBEventPtr) {
        case Vptr(eid):
            abstcb.prio == tcb.OSTCBPrio &&
            abstcb.stat == wait(os_stat_mbox(eid), tcb.OSTCBDly) &&
            abstcb.sus == true;
        default: true;
    }
}

predicate RHL_WaitMB_Suspend_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_mbox(eid), dly), sus: true}}:
            tcb.OSTCBPrio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.OSTCBEventPtr == Vptr(eid) && tcb.OSTCBStat == OS_STAT_MBOX | OS_STAT_SUSPEND;
        default: true;
    }
}

// mutex case
predicate RLH_WaitMS_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBStat == OS_STAT_MUTEX ->
    switch (tcb.OSTCBEventPtr) {
        case Vptr(eid):
            abstcb.prio == tcb.OSTCBPrio &&
            abstcb.stat == wait(os_stat_mutexsem(eid), tcb.OSTCBDly) &&
            abstcb.sus == false;
        default: true;
    }
}

predicate RHL_WaitMS_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_mutexsem(eid), dly), sus: false}}:
            tcb.OSTCBPrio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.OSTCBEventPtr == Vptr(eid) && tcb.OSTCBStat == OS_STAT_MUTEX;
        default: true;
    }
}

predicate RLH_WaitMS_Suspend_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.OSTCBPrio, rtbl) -> tcb.OSTCBStat == OS_STAT_MUTEX | OS_STAT_SUSPEND ->
    switch (tcb.OSTCBEventPtr) {
        case Vptr(eid):
            abstcb.prio == tcb.OSTCBPrio &&
            abstcb.stat == wait(os_stat_mutexsem(eid), tcb.OSTCBDly) &&
            abstcb.sus == true;
        default: true;
    }
}

predicate RHL_WaitMS_Suspend_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_mutexsem(eid), dly), sus: true}}:
            tcb.OSTCBPrio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.OSTCBEventPtr == Vptr(eid) && tcb.OSTCBStat == OS_STAT_MUTEX | OS_STAT_SUSPEND;
        default: true;
    }
}

// all low-to-high: wait for event
predicate RLH_TCB_Status_Wait_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    RLH_Wait_P(tcb, rtbl, abstcb) &&
    RLH_WaitS_P(tcb, rtbl, abstcb) &&
    RLH_WaitQ_P(tcb, rtbl, abstcb) &&
    RLH_WaitMB_P(tcb, rtbl, abstcb) &&
    RLH_WaitMS_P(tcb, rtbl, abstcb) &&
    RLH_WaitS_Suspend_P(tcb, rtbl, abstcb) &&
    RLH_WaitQ_Suspend_P(tcb, rtbl, abstcb) &&
    RLH_WaitMB_Suspend_P(tcb, rtbl, abstcb) &&
    RLH_WaitMS_Suspend_P(tcb, rtbl, abstcb)
}

// all high-to-low: wait for event
predicate RHL_TCB_Status_Wait_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    RHL_Wait_P(tcb, rtbl, abstcb) &&
    RHL_WaitS_P(tcb, rtbl, abstcb) &&
    RHL_WaitQ_P(tcb, rtbl, abstcb) &&
    RHL_WaitMB_P(tcb, rtbl, abstcb) &&
    RHL_WaitMS_P(tcb, rtbl, abstcb) &&
    RHL_WaitS_Suspend_P(tcb, rtbl, abstcb) &&
    RHL_WaitQ_Suspend_P(tcb, rtbl, abstcb) &&
    RHL_WaitMB_Suspend_P(tcb, rtbl, abstcb) &&
    RHL_WaitMS_Suspend_P(tcb, rtbl, abstcb)
}

// all refinement relations
predicate R_TCB_Status_P(TCB tcb, Seq<int8u> rtbl, AbsTCB abstcb) {
    RLH_RdyI_P(tcb, rtbl, abstcb) &&
    RHL_RdyI_P(tcb, rtbl, abstcb) &&
    RLH_Suspend_P(tcb, rtbl, abstcb) &&
    RHL_Suspend_P(tcb, rtbl, abstcb) &&
    RLH_TCB_Status_Wait_P(tcb, rtbl, abstcb) &&
    RHL_TCB_Status_Wait_P(tcb, rtbl, abstcb)
}

/*
 * Invariant relating the priority map and the priority groups.
 *
 * For each index n between 0 and 7, the corresponding bit in grp is on
 * if and only if the corresponding index in rtbl is nonzero.
 */
predicate RL_Tbl_Grp_P(Global global) {
    |global.OSRdyTbl| == 8 &&
    forall (int8u n in range8(0, 8)) {
        (global.OSRdyGrp & (1 << n) == 0) ==
            (global.OSRdyTbl[int(n)] == 0) &&
        (global.OSRdyGrp & (1 << n) == 1 << n) ==
            (global.OSRdyTbl[int(n)] > 0)
    }
}

/*
 * Unset priority in tcb from the priority map.
 */
function unset_bitmap_prio(Global global, TCB tcb) -> Global {
    let y = int(tcb.OSTCBY) in
    let bitx = tcb.OSTCBBitX in
    let global2 = global{|OSRdyTbl[y] := global.OSRdyTbl[y] & ~bitx|} in
        if (global2.OSRdyTbl[y] == 0) {
            global2{OSRdyGrp := global2.OSRdyGrp & ~tcb.OSTCBBitY}
        } else {
            global2
        }
    end
    end
    end
}

/*
 * Set priority in tcb onto the priority map.
 */
function set_bitmap_prio(Global global, TCB tcb) -> Global {
    let y = int(tcb.OSTCBY) in
    let bitx = tcb.OSTCBBitX in
    let global2 = global{OSRdyGrp := global.OSRdyGrp | tcb.OSTCBBitY} in
        global2{|OSRdyTbl[y] := global.OSRdyTbl[y] | bitx|}
    end
    end
    end
}

/*
 * Function unset_bitmap_prio preserves RL_Tbl_Grp_P.
 */
query unset_bitmap_prio_RL_Tbl_Grp_P {
    fixes tcb : TCB;
    fixes global : Global;
    fixes global2 : Global;
    assumes global2 == unset_bitmap_prio(global, tcb);
    assumes RL_TCBblk_P(tcb);
    assumes H: RL_Tbl_Grp_P(global);
    shows RL_Tbl_Grp_P(global2)
    proof { seq_auto }
}

/*
 * Function unset_bitmap_prio unset priority.
 */
query unset_bitmap_prio_RL_Tbl_Grp_P2 {
    fixes tcb : TCB;
    fixes global : Global;
    fixes global2 : Global;
    assumes global2 == unset_bitmap_prio(global, tcb);
    assumes RL_TCBblk_P(tcb);
    shows prio_not_in_tbl(tcb.OSTCBPrio, global2.OSRdyTbl)
    proof { seq_auto }
}

/*
 * Function set_bitmap_prio preserves RL_Tbl_Grp_P.
 */
query set_bitmap_prio_RL_Tbl_Grp_P {
    fixes tcb : TCB;
    fixes global : Global;
    fixes global2 : Global;
    assumes global2 == set_bitmap_prio(global, tcb);
    assumes RL_TCBblk_P(tcb);
    assumes RL_Tbl_Grp_P(global);
    shows RL_Tbl_Grp_P(global2)
    proof { seq_auto }
}

/*
 * Function set_bitmap_prio set priority.
 */
query set_bitmap_prio_RL_Tbl_Grp_P2 {
    fixes tcb : TCB;
    fixes global : Global;
    fixes global2 : Global;
    assumes global2 == set_bitmap_prio(global, tcb);
    assumes RL_TCBblk_P(tcb);
    shows prio_in_tbl(tcb.OSTCBPrio, global2.OSRdyTbl)
    proof { seq_auto }
}

/*
 * Low-level invariant on OSTCBPrioTbl and priority table.
 *
 * 1. Priority is in the priority table iff it is in OSTCBPrioTbl.
 * 2. Each entry in OSTCBPrioTbl has right priority and obeys its invariant.
 */
predicate RL_TCB_P(Global global) {
    forall (int8u prio in range8(0, 64)) {
        if (!indom(prio, global.OSTCBPrioTbl)) {
            prio_not_in_tbl(prio, global.OSRdyTbl)
        } else {
            let tcb = get(prio, global.OSTCBPrioTbl) in
                tcb.OSTCBPrio == prio &&
                RL_TCBblk_P(tcb)
            end
        }
    }
}

/*
 * Refinement relation between OSTCBPrioTbl and tcbMap.
 *
 * 1. They contain entries at the same priorities.
 * 2. The corresponding elements satisfy refinement relation R_TCB_Status_P.
 */
predicate RLH_TCB_P(Global global, AbsGlobal absGlobal) {
    forall (int8u prio in range8(0, 64)) {
        if (!indom(prio, global.OSTCBPrioTbl)) {
            !indom(prio, absGlobal.tcbMap)
        } else {
            indom(prio, absGlobal.tcbMap) &&
            let tcb = get(prio, global.OSTCBPrioTbl) in
            let abstcb = get(prio, absGlobal.tcbMap) in
                R_TCB_Status_P(tcb, global.OSRdyTbl, abstcb)
            end
            end
        }
    }
}

query RL_TCBblk_P_suspend {
    fixes tcb : TCB;
    assumes RL_TCBblk_P(tcb);
    shows RL_TCBblk_P(tcb{OSTCBStat := tcb.OSTCBStat | OS_STAT_SUSPEND})
    proof { seq_auto }
}

function OSTaskSuspend(int8u prio, Global global) -> Global {
    if (!indom(prio, global.OSTCBPrioTbl)) {
        global
    } else {
        let tcb = get(prio, global.OSTCBPrioTbl) in
        let global2 = unset_bitmap_prio(global, tcb) in
            global2{|OSTCBPrioTbl[prio].OSTCBStat := tcb.OSTCBStat | OS_STAT_SUSPEND|}
        end
        end
    }
}

function OSTaskSuspendAbs(int8u prio, AbsGlobal absGlobal) -> AbsGlobal {
    if (!indom(prio, absGlobal.tcbMap)) {
        absGlobal
    } else {
        absGlobal{|tcbMap[prio].sus := true|}
    }
}

query R_TCB_Status_P_suspend {
    fixes tcb : TCB;
    fixes rtbl : Seq<int8u>;
    fixes rtbl2 : Seq<int8u>;
    fixes abstcb : AbsTCB;
    assumes prio_not_in_tbl(tcb.OSTCBPrio, rtbl2);
    assumes R_TCB_Status_P(tcb, rtbl, abstcb);
    shows R_TCB_Status_P(tcb{OSTCBStat := tcb.OSTCBStat | OS_STAT_SUSPEND}, rtbl2, abstcb{sus := true})
    proof { seq_auto }
}

query RLH_TCB_P_suspend1 {
    fixes global: Global;
    fixes prio: int8u;
    fixes global2: Global;
    assumes global2 == OSTaskSuspend(prio, global);
    assumes prio >= 0 && prio < 64;
    assumes H2: RL_TCB_P(global);
    assumes H3: RL_Tbl_Grp_P(global);
    shows RL_TCB_P(global2)
    proof { seq_auto }
}

query RLH_TCB_P_suspend2 {
    fixes global: Global;
    fixes prio: int8u;
    fixes global2: Global;
    assumes global2 == OSTaskSuspend(prio, global);
    assumes prio >= 0 && prio < 64;
    assumes H2: RL_TCB_P(global);
    assumes H3: RL_Tbl_Grp_P(global);
    shows RL_Tbl_Grp_P(global2)
    proof { seq_auto }
}

query RLH_TCB_P_suspend3 {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes prio: int8u;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    assumes global2 == OSTaskSuspend(prio, global);
    assumes absGlobal2 == OSTaskSuspendAbs(prio, absGlobal);
    assumes prio >= 0 && prio < 64;
    assumes H1: RLH_TCB_P(global, absGlobal);
    assumes H2: RL_TCB_P(global);
    assumes H3: RL_Tbl_Grp_P(global);
    shows RLH_TCB_P(global2, absGlobal2)
    proof { seq_auto }
}

function OSTaskResume(int8u prio, Global global) -> Global {
    if (!indom(prio, global.OSTCBPrioTbl)) {
        global
    } else {
        let tcb = get(prio, global.OSTCBPrioTbl) in
            if (tcb.OSTCBStat & OS_STAT_SUSPEND != OS_STAT_RDY) {
                let global2 = global{|OSTCBPrioTbl[prio].OSTCBStat := tcb.OSTCBStat & ~OS_STAT_SUSPEND|} in
                let tcb2 = get(prio, global2.OSTCBPrioTbl) in
                    if (tcb2.OSTCBStat == OS_STAT_RDY && tcb2.OSTCBDly == 0) {
                        set_bitmap_prio(global2, tcb2)
                    } else {
                        global2
                    }
                end
                end
            } else {
                global
            }
        end
    }
}

function OSTaskResumeAbs(int8u prio, AbsGlobal absGlobal) -> AbsGlobal {
    if (!indom(prio, absGlobal.tcbMap)) {
        absGlobal
    } else {
        absGlobal{|tcbMap[prio].sus := false|}
    }
}

query RLH_TCB_P_resume1 {
    fixes global: Global;
    fixes prio: int8u;
    fixes global2: Global;
    assumes global2 == OSTaskResume(prio, global);
    assumes prio >= 0 && prio < 64;
    assumes H2: RL_TCB_P(global);
    assumes H3: RL_Tbl_Grp_P(global);
    shows RL_TCB_P(global2)
    proof { seq_auto }
}

query RLH_TCB_P_resume2 {
    fixes global: Global;
    fixes prio: int8u;
    fixes global2: Global;
    assumes global2 == OSTaskResume(prio, global);
    assumes prio >= 0 && prio < 64;
    assumes H2: RL_TCB_P(global);
    assumes H3: RL_Tbl_Grp_P(global);
    shows RL_Tbl_Grp_P(global2)
    proof { seq_auto }
}

query RLH_TCB_P_resume3 {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes prio: int8u;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    assumes global2 == OSTaskResume(prio, global);
    assumes absGlobal2 == OSTaskResumeAbs(prio, absGlobal);
    assumes prio >= 0 && prio < 64;
    assumes H1: RLH_TCB_P(global, absGlobal);
    assumes H2: RL_TCB_P(global);
    assumes H3: RL_Tbl_Grp_P(global);
    shows RLH_TCB_P(global2, absGlobal2)
    proof { seq_auto }
}

/*
 * Refinement relation between low-level queue and high-level
 * message list.
 */
predicate MatchLHMsgList(OS_Q q, Seq<addrval> msgl) {
    let qin = q.OSQIn in
    let qout = q.OSQOut in
    let qens = q.OSQEntries in
    let msgtbl = q.OSQData in
    let qsize = |msgtbl| in
        0 <= qin && qin < qsize &&
        0 <= qout && qout < qsize &&
        (qin > qout -> msgl == msgtbl[qout:qin] &&
                       qens == qin - qout) &&
        (qin < qout -> msgl == msgtbl[qout:qsize] ++ msgtbl[0:qin] &&
                       qens == (qsize - qout) + qin) &&
        (qout == qin -> qens == 0 || qens == qsize) &&
        (qout == qin -> qens == 0 -> msgl == []) &&
        (qout == qin && qens == qsize ->
         msgl == msgtbl[qout:qsize] ++ msgtbl[0:qin])
    end
    end
    end
    end
    end
}

query HighestPrio {
    fixes global: Global;
    fixes x: int8u;
    fixes y: int8u;
    fixes prio: int8u;
    assumes y == OSUnMapTbl[int(global.OSRdyGrp)];
    assumes x == OSUnMapTbl[int(global.OSRdyTbl[int(y)])];
    assumes prio == (y << 3) + x;
    assumes RL_Tbl_Grp_P(global);
    assumes global.OSRdyGrp != 0;
    shows forall (int8u prio1) {
        prio1 < prio -> prio_not_in_tbl(prio1, global.OSRdyTbl)
    } && prio_in_tbl(prio, global.OSRdyTbl)
    proof { seq_auto }
}

/*
 * Set priority in event priority map.
 */
function set_event_bitmap_prio(Global global, address pevent, TCB tcb) -> Global {
    let y = int(tcb.OSTCBY) in
    let bitx = tcb.OSTCBBitX in
    let global2 = global{|events[pevent].OSEventGrp := get(pevent, global.events).OSEventGrp | tcb.OSTCBBitY|} in
        global2{|events[pevent].OSEventTbl[y] := get(pevent, global2.events).OSEventTbl[y] | bitx|}
    end
    end
    end
}

/*
 * Unset priority in event priority map.
 */
function unset_event_bitmap_prio(Global global, address pevent, TCB tcb) -> Global {
    let y = int(tcb.OSTCBY) in
    let bitx = tcb.OSTCBBitX in
    let global2 = global{|events[pevent].OSEventTbl[y] := get(pevent, global.events).OSEventTbl[y] & ~bitx|} in
        if (get(pevent, global2.events).OSEventTbl[y] == 0) {
            global2{|events[pevent].OSEventGrp := get(pevent, global2.events).OSEventGrp & ~tcb.OSTCBBitY|}
        } else {
            global2
        }
    end
    end
    end
}

function OS_EventTaskWait(Global global, address pevent) -> Global {
    let global2 = global{|OSTCBPrioTbl[global.OSPrioCur].OSTCBEventPtr := Vptr(pevent)|} in
    let global3 = unset_bitmap_prio(global2, get(global.OSPrioCur, global.OSTCBPrioTbl)) in
        set_event_bitmap_prio(global3, pevent, get(global.OSPrioCur, global.OSTCBPrioTbl))
    end
    end
}

function OS_EventTO(Global global, address pevent) -> Global {
    let global2 = unset_event_bitmap_prio(global, pevent, get(global.OSPrioCur, global.OSTCBPrioTbl)) in
    let global3 = global2{|OSTCBPrioTbl[global.OSPrioCur].OSTCBStat := OS_STAT_RDY|} in
        global3{|OSTCBPrioTbl[global.OSPrioCur].OSTCBEventPtr := Vnull|}
    end
    end
}

function OS_EventTaskRdy(Global global, address pevent, addrval msg, int16u msk) -> Global {
    let event = get(pevent, global.events) in
    let y = OSUnMapTbl[int(event.OSEventGrp)] in
    let x = OSUnMapTbl[int(event.OSEventTbl[int(y)])] in
    let prio = (y << 3) + x in
    let ptcb = get(prio, global.OSTCBPrioTbl) in
    let global2 = unset_event_bitmap_prio(global, pevent, ptcb) in
    let global3 = global2{|OSTCBPrioTbl[prio].OSTCBDly := 0|} in
    let global4 = global3{|OSTCBPrioTbl[prio].OSTCBEventPtr := Vnull|} in
    let global5 = global4{|OSTCBPrioTbl[prio].OSTCBMsg := msg|} in
    let global6 = global5{|OSTCBPrioTbl[prio].OSTCBStat := get(prio, global5.OSTCBPrioTbl).OSTCBStat & ~msk|} in
        if (get(prio, global6.OSTCBPrioTbl).OSTCBStat == OS_STAT_RDY) {
            set_bitmap_prio(global6, ptcb)
        } else {
            global6
        }
    end
    end
    end
    end
    end
    end
    end
    end
    end
    end
}

/*
 * First part of OSSemPend (before OS_Sched).
 *
 * Assume pevent is in global.events and the event type is OS_EVENT_TYPE_SEM.
 */
function OSSemPend1(Global global, address pevent, int16u timeout) -> Global {
    if (get(pevent, global.events).OSEventCnt > 0) {
        global{|events[pevent].OSEventCnt := get(pevent, global.events).OSEventCnt - 1|}
    } else {
        let global2 = global{|OSTCBPrioTbl[global.OSPrioCur].OSTCBStat :=
                              get(global.OSPrioCur, global.OSTCBPrioTbl).OSTCBStat | OS_STAT_SEM|} in
        let global3 = global2{|OSTCBPrioTbl[global.OSPrioCur].OSTCBDly := timeout|} in
            OS_EventTaskWait(global3, pevent)
        end
        end
    }
}

/*
 * Second part of OSSemPend (after OS_Sched)
 */
function OSSemPend2(Global global, address pevent) -> Global {
    if (get(global.OSPrioCur, global.OSTCBPrioTbl).OSTCBStat & OS_STAT_SEM != 0) {
        OS_EventTO(global, pevent)
    } else {
        global{|OSTCBPrioTbl[global.OSPrioCur].OSTCBEventPtr := Vnull|}
    }
}

/*
 * Part of OSSemPost before OS_Sched.
 */
function OSSemPost(Global global, address pevent) -> Global {
    let event = get(pevent, global.events) in
        if (event.OSEventGrp != 0) {
            OS_EventTaskRdy(global, pevent, Vnull, OS_STAT_SEM)
        } else {
            if (event.OSEventCnt < 65535) {
                global{|events[pevent].OSEventCnt := event.OSEventCnt + 1|}
            } else {
                global
            }
        }
    end
}

/*
 * Invariant on high-level event information.
 *
 * For message queue, semaphore and mailbox, correspondence between waitset
 * being empty with other information.
 *
 * For mutex, additional constraints on priority inheritance. The priority of
 * the mutex is higher (smaller value) than the original priority of owning task.
 */
predicate RH_ECB_P (AbsECB absecb) {
    switch (absecb.edata) {
        case absmsgq(msgl, qsize):
            (|msgl| > 0 -> |absecb.wset| == 0) &&
            (|absecb.wset| > 0 -> |msgl| == 0);
        case abssem(count):
            (count > 0 -> |absecb.wset| == 0) &&
            (|absecb.wset| > 0 -> count == 0);
        case absmbox(msg):
            (msg != Vnull -> |absecb.wset| == 0) &&
            (|absecb.wset| > 0 -> msg == Vnull);
        case absmutexsem(prio, oprio, owned):
            (owned == false -> |absecb.wset| == 0) &&
            (owned == true -> prio < oprio && oprio < 64) &&
            (|absecb.wset| > 0 -> owned == true) &&
            prio < 64;
    }
}

predicate RH_ECB_P_All(AbsGlobal absGlobal) {
    forall (address eid in absGlobal.ecbMap) {
        RH_ECB_P(get(eid, absGlobal.ecbMap))
    }
}

/*
 * Refinement relation between low-level and high-level event information.
 *
 * Unlike in the Coq proof, we skip the use of intermediate datatype
 * EventData. Correspondence of EventData with low-level data is recorded
 * as follows (AEventData):
 *
 * DMsgQ(a, osq, osqblk, msgtbl):
 *  a: OSEventPtr
 * DSem(z):
 *  z: OSEventCnt, z < 65536
 * DMbox(msg):
 *  msg: OSEventPtr
 * DMutex(a, b):
 *  a: OSEventCnt (lower 8-bits is oprio, upper 8-bits is prio)
 *  b: OSEventPtr 
 */
predicate RLH_ECBData_P (EVENT event, AbsECB absecb) {
    switch (absecb.edata) {
        case absmsgq(msgl, qsize):
            event.OSEventType == OS_EVENT_TYPE_Q &&
            switch (event.OSQueue) {
                case none: false;
                case some(queue):
                    MatchLHMsgList(queue, msgl) &&
                    queue.OSQEntries == |msgl| &&
                    |queue.OSQData| == qsize;
            };
        case abssem(count):
            event.OSEventType == OS_EVENT_TYPE_SEM &&
            event.OSEventCnt == count &&
            0 <= count && count < 65536;
        case absmbox(msg):
            event.OSEventType == OS_EVENT_TYPE_MBOX &&
            event.OSEventPtr == msg;
        case absmutexsem(prio, oprio, owned):
            event.OSEventType == OS_EVENT_TYPE_MUTEX &&
            event.OSEventCnt >> 8 == prio &&
            if (event.OSEventCnt & 255 == 255) {
                owned == false
            } else {
                event.OSEventCnt & 255 == oprio
                // TODO: investigate whether OSEventPtr is needed
            };
    }
}

predicate RLH_ECBData_P_All(Global global, AbsGlobal absGlobal) {
    forall (address eid in global.events) {
        indom(eid, absGlobal.ecbMap) &&
        RLH_ECBData_P(get(eid, global.events), get(eid, absGlobal.ecbMap))
    } &&
    forall (address eid in absGlobal.ecbMap) {
        indom(eid, global.events)
    }
}

/*
 * The following series of predicates relate the high-level task and event
 * information.
 *
 * They state that a task is in the waiting set of some event info, iff
 * the task has the corresponding waiting status.
 */
predicate RH_TCBList_ECBList_P1(AbsGlobal absGlobal) {
    forall (address eid in absGlobal.ecbMap) {
        let absecb = get(eid, absGlobal.ecbMap) in
            forall (int i) {
                0 <= i && i < |absecb.wset| ->
                indom(absecb.wset[i], absGlobal.tcbMap) &&
                switch (absecb.edata) {
                    case absmsgq(msgl, qsize):
                        switch (get(absecb.wset[i], absGlobal.tcbMap)) {
                            case AbsTCB{{stat: wait(os_stat_q(eid2), dly)}}:
                                eid == eid2;
                            default: false;
                        };
                    case abssem(count):
                        switch (get(absecb.wset[i], absGlobal.tcbMap)) {
                            case AbsTCB{{stat: wait(os_stat_sem(eid2), dly)}}:
                                eid == eid2;
                            default: false;
                        };
                    case absmbox(msg):
                        switch (get(absecb.wset[i], absGlobal.tcbMap)) {
                            case AbsTCB{{stat: wait(os_stat_mbox(eid2), dly)}}:
                                eid == eid2;
                            default: false;
                        };
                    case absmutexsem(prio, oprio, owned):
                        switch (get(absecb.wset[i], absGlobal.tcbMap)) {
                            case AbsTCB{{stat: wait(os_stat_mutexsem(eid2), dly)}}:
                                eid == eid2;
                            default: false;
                        };
                }
            }
        end
    }
}

predicate RH_TCBList_ECBList_P2(AbsGlobal absGlobal) {
    forall (int8u prio in range8(0, 64)) {
        indom(prio, absGlobal.tcbMap) ->
        switch (get(prio, absGlobal.tcbMap)) {
            case AbsTCB{{stat: wait(os_stat_q(eid), dly)}}:
                indom(eid, absGlobal.ecbMap) &&
                switch (get(eid, absGlobal.ecbMap)) {
                    case AbsECB{{edata: absmsgq(msgl, qsize), wset: wset}}:
                        exists (int j) {
                            0 <= j && j < |wset| && wset[j] == prio
                        };
                    default: false;
                };
            case AbsTCB{{stat: wait(os_stat_sem(eid), dly)}}:
                indom(eid, absGlobal.ecbMap) &&
                switch (get(eid, absGlobal.ecbMap)) {
                    case AbsECB{{edata: abssem(count), wset: wset}}:
                        exists (int j) {
                            0 <= j && j < |wset| && wset[j] == prio
                        };
                    default: false;
                };
            case AbsTCB{{stat: wait(os_stat_mbox(eid), dly)}}:
                indom(eid, absGlobal.ecbMap) &&
                switch (get(eid, absGlobal.ecbMap)) {
                    case AbsECB{{edata: absmbox(msg), wset: wset}}:
                        exists (int j) {
                            0 <= j && j < |wset| && wset[j] == prio
                        };
                    default: false;
                };
            case AbsTCB{{stat: wait(os_stat_mutexsem(eid), dly)}}:
                indom(eid, absGlobal.ecbMap) &&
                switch (get(eid, absGlobal.ecbMap)) {
                    case AbsECB{{edata: absmutexsem(prio2, oprio, owned), wset: wset}}:
                        exists (int j) {
                            0 <= j && j < |wset| && wset[j] == prio
                        };
                    default: false;
                };
            default:
                true;
        }
    }
}

/*
 * Abstract version of OSSemPend1.
 *
 * Assume pevent is in absGlobal.ecbMap.
 */
function OSSemPendAbs1(AbsGlobal absGlobal, address pevent, int16u timeout) -> AbsGlobal {
    switch (get(pevent, absGlobal.ecbMap)) {
        case AbsECB{{edata: abssem(count), wset: wset}}:
            if (count > 0) {
                absGlobal{|ecbMap[pevent].edata := abssem(count - 1)|}
            } else {
                let absGlobal2 = absGlobal{|ecbMap[pevent] :=
                    AbsECB{{edata: abssem(0),
                            wset: seq_cons(absGlobal.curTask, get(pevent, absGlobal.ecbMap).wset)}}|} in
                    absGlobal2{|tcbMap[absGlobal.curTask].stat := wait(os_stat_sem(pevent), timeout)|}
                end
            };
        default:
            absGlobal;
    }
}

query OSSemPend1_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes timeout: int16u;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSSemPendAbs1(absGlobal, pevent, timeout);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

predicate RH_CurTask_Ready(AbsGlobal absGlobal) {
    switch (get(absGlobal.curTask, absGlobal.tcbMap)) {
        case AbsTCB{{stat: rdy, sus: false}}:
            true;
        default:
            false;
    }
}

query OSSemPend1_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes timeout: int16u;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSSemPendAbs1(absGlobal, pevent, timeout);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSSemPend1_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes timeout: int16u;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSSemPendAbs1(absGlobal, pevent, timeout);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSSemPend1_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes timeout: int16u;
    fixes pevent: address;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_SEM;
    assumes global2 == OSSemPend1(global, pevent, timeout);
    assumes absGlobal2 == OSSemPendAbs1(absGlobal, pevent, timeout);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

/*
 * Abstract version of OSSemPend2.
 */
function OSSemPendAbs2(AbsGlobal absGlobal, address pevent) -> AbsGlobal {
    absGlobal{|tcbMap[absGlobal.curTask].stat := rdy|}
}

query OSSemPend2_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSSemPendAbs2(absGlobal, pevent);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSSemPend2_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSSemPendAbs2(absGlobal, pevent);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSSemPend2_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSSemPendAbs2(absGlobal, pevent);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSSemPend2_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes pevent: address;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_SEM;
    assumes global2 == OSSemPend2(global, pevent);
    assumes absGlobal2 == OSSemPendAbs2(absGlobal, pevent);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

/*
 * Abstract version of OSSemPost.
 *
 * When posting to a semaphore, the task with highest priority is
 * removed from waiting list. That task is readied. If there are
 * no tasks in the waiting list, the semaphore count is increased
 * by 1 (up to 65535).
 */
function OSSemPostAbsHelper(AbsGlobal absGlobal, address pevent, int highPrioId) -> AbsGlobal {
    let highPrio = get(pevent, absGlobal.ecbMap).wset[highPrioId] in
    let absGlobal2 = absGlobal{|ecbMap[pevent].wset :=
            seq_remove(highPrioId, get(pevent, absGlobal.ecbMap).wset)|} in
        absGlobal2{|tcbMap[highPrio].stat := rdy|}
    end
    end
}

predicate unique_prio(Seq<int8u> a) {
    forall (int i, int j) {
        0 <= i && i < |a| &&
        0 <= j && j < |a| && i != j -> a[i] != a[j]
    }
}

predicate event_wset_unique(AbsGlobal absGlobal) {
    forall (address pevent in absGlobal.ecbMap) {
        unique_prio(get(pevent, absGlobal.ecbMap).wset)
    }
}

predicate highPrioIdInWset(Seq<int8u> wset, int highPrioId) {
    0 <= highPrioId && highPrioId < |wset| &&
    forall (int i) {
        0 <= i && i < |wset| -> wset[highPrioId] <= wset[i]
    }
}

predicate OSSemPostAbs1(AbsGlobal absGlobal, AbsGlobal absGlobal2, address pevent) {
    exists (int highPrioId) {
        highPrioIdInWset(get(pevent, absGlobal.ecbMap).wset, highPrioId) &&
        absGlobal2 == OSSemPostAbsHelper(absGlobal, pevent, highPrioId)
    }
}

query OSSemPost1_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| > 0;
    assumes OSSemPostAbs1(absGlobal, absGlobal2, pevent);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSSemPost1_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| > 0;
    assumes OSSemPostAbs1(absGlobal, absGlobal2, pevent);
    assumes event_wset_unique(absGlobal);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSSemPost1_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| > 0;
    assumes OSSemPostAbs1(absGlobal, absGlobal2, pevent);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSSemPost1_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes pevent: address;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventGrp != 0;
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_SEM;
    assumes global2 == OSSemPost(global, pevent);
    assumes OSSemPostAbs1(absGlobal, absGlobal2, pevent);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

function OSSemPostAbs2(AbsGlobal absGlobal, address pevent) -> AbsGlobal {
    switch (get(pevent, absGlobal.ecbMap)) {
        case AbsECB{{edata: abssem(count), wset: wset}}:
            if (count < 65535) {
                absGlobal{|ecbMap[pevent].edata := abssem(count + 1)|}
            } else {
                absGlobal
            };
        default: absGlobal;
    }
}

query OSSemPost2_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| == 0;
    assumes absGlobal2 == OSSemPostAbs2(absGlobal, pevent);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSSemPost2_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSSemPostAbs2(absGlobal, pevent);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSSemPost2_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSSemPostAbs2(absGlobal, pevent);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSSemPost2_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes pevent: address;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventGrp == 0;
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_SEM;
    assumes global2 == OSSemPost(global, pevent);
    assumes absGlobal2 == OSSemPostAbs2(absGlobal, pevent);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

/*
 * First part of OSMboxPend (before OS_Sched).
 *
 * Assume pevent is in global.events and the event type is OS_EVENT_TYPE_MBOX.
 */
function OSMboxPend1(Global global, address pevent, int16u timeout) -> Global {
    if (get(pevent, global.events).OSEventPtr != Vnull) {
        let msg = get(pevent, global.events).OSEventPtr in
        let global2 = global{|events[pevent].OSEventPtr := Vnull|} in
            global2{|OSTCBPrioTbl[global.OSPrioCur].OSTCBMsg := msg|}
        end
        end
    } else {
        let global2 = global{|OSTCBPrioTbl[global.OSPrioCur].OSTCBStat :=
                              get(global.OSPrioCur, global.OSTCBPrioTbl).OSTCBStat | OS_STAT_MBOX|} in
        let global3 = global2{|OSTCBPrioTbl[global.OSPrioCur].OSTCBDly := timeout|} in
            OS_EventTaskWait(global3, pevent)
        end
        end
    }
}

/*
 * Second part of OSMboxPend (after OS_Sched).
 */
function OSMboxPend2(Global global, address pevent) -> Global {
    if (get(global.OSPrioCur, global.OSTCBPrioTbl).OSTCBMsg == Vnull) {
        OS_EventTO(global, pevent)
    } else {
        let global2 = global{|OSTCBPrioTbl[global.OSPrioCur].OSTCBMsg := Vnull|} in
        let global3 = global2{|OSTCBPrioTbl[global.OSPrioCur].OSTCBStat := OS_STAT_RDY|} in
            global3{|OSTCBPrioTbl[global.OSPrioCur].OSTCBEventPtr := Vnull|}
        end
        end
    }
}

/*
 * Part of OSMboxPost before OS_Sched.
 *
 * Assume msg is not null.
 */
function OSMboxPost(Global global, address pevent, addrval msg) -> Global {
    let event = get(pevent, global.events) in
        if (event.OSEventGrp != 0) {
            OS_EventTaskRdy(global, pevent, msg, OS_STAT_MBOX)
        } else {
            if (event.OSEventPtr != Vnull) {
                global
            } else {
                global{|events[pevent].OSEventPtr := msg|}
            }
        }
    end
}

/*
 * Abstract version of OSMboxPend1.
 *
 * Assume pevent is in absGlobal.ecbMap.
 */
function OSMboxPendAbs1(AbsGlobal absGlobal, address pevent, int16u timeout) -> AbsGlobal {
    switch (get(pevent, absGlobal.ecbMap)) {
        case AbsECB{{edata: absmbox(msg), wset: wset}}:
            if (msg != Vnull) {
                let absGlobal2 = absGlobal{|ecbMap[pevent].edata := absmbox(Vnull)|} in
                    absGlobal2{|tcbMap[absGlobal.curTask].msg := msg|}
                end
            } else {
                let absGlobal2 = absGlobal{|ecbMap[pevent] :=
                    AbsECB{{edata: absmbox(Vnull),
                            wset: seq_cons(absGlobal.curTask, get(pevent, absGlobal.ecbMap).wset)}}|} in
                    absGlobal2{|tcbMap[absGlobal.curTask].stat := wait(os_stat_mbox(pevent), timeout)|}
                end
            };
        default:
            absGlobal;
    }
}

query OSMboxPend1_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes timeout: int16u;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSMboxPendAbs1(absGlobal, pevent, timeout);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSMboxPend1_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes timeout: int16u;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSMboxPendAbs1(absGlobal, pevent, timeout);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSMboxPend1_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes timeout: int16u;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSMboxPendAbs1(absGlobal, pevent, timeout);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSMboxPend1_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes timeout: int16u;
    fixes pevent: address;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_MBOX;
    assumes global2 == OSMboxPend1(global, pevent, timeout);
    assumes absGlobal2 == OSMboxPendAbs1(absGlobal, pevent, timeout);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

/*
 * Abstract version of OSMboxPend2.
 */
function OSMboxPendAbs2(AbsGlobal absGlobal, address pevent) -> AbsGlobal {
    let absGlobal2 = absGlobal{|tcbMap[absGlobal.curTask].msg := Vnull|} in
        absGlobal2{|tcbMap[absGlobal.curTask].stat := rdy|}
    end
}

query OSMboxPend2_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSMboxPendAbs2(absGlobal, pevent);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSMboxPend2_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSMboxPendAbs2(absGlobal, pevent);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSMboxPend2_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSMboxPendAbs2(absGlobal, pevent);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSMboxPend2_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes pevent: address;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_MBOX;
    assumes global2 == OSMboxPend2(global, pevent);
    assumes absGlobal2 == OSMboxPendAbs2(absGlobal, pevent);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

/*
 * Abstract version of OSMboxPost.
 */
function OSMboxPostAbsHelper(AbsGlobal absGlobal, address pevent, int highPrioId, addrval msg) -> AbsGlobal {
    let highPrio = get(pevent, absGlobal.ecbMap).wset[highPrioId] in
    let absGlobal2 = absGlobal{|ecbMap[pevent].wset :=
            seq_remove(highPrioId, get(pevent, absGlobal.ecbMap).wset)|} in
    let absGlobal3 = absGlobal2{|tcbMap[highPrio].stat := rdy|} in
        absGlobal3{|tcbMap[highPrio].msg := msg|}
    end
    end
    end
}

predicate OSMboxPostAbs1(AbsGlobal absGlobal, AbsGlobal absGlobal2, address pevent, addrval msg) {
    exists (int highPrioId) {
        highPrioIdInWset(get(pevent, absGlobal.ecbMap).wset, highPrioId) &&
        absGlobal2 == OSMboxPostAbsHelper(absGlobal, pevent, highPrioId, msg)
    }
}

query OSMboxPost1_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    fixes msg: addrval;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| > 0;
    assumes OSMboxPostAbs1(absGlobal, absGlobal2, pevent, msg);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSMboxPost1_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    fixes msg: addrval;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| > 0;
    assumes OSMboxPostAbs1(absGlobal, absGlobal2, pevent, msg);
    assumes event_wset_unique(absGlobal);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSMboxPost1_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    fixes msg: addrval;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| > 0;
    assumes OSMboxPostAbs1(absGlobal, absGlobal2, pevent, msg);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSMboxPost1_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventGrp != 0;
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_MBOX;
    assumes global2 == OSMboxPost(global, pevent, msg);
    assumes OSMboxPostAbs1(absGlobal, absGlobal2, pevent, msg);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

function OSMboxPostAbs2(AbsGlobal absGlobal, address pevent, addrval msg_in) -> AbsGlobal {
    switch (get(pevent, absGlobal.ecbMap)) {
        case AbsECB{{edata: absmbox(msg), wset: wset}}:
            if (msg != Vnull) {
                absGlobal
            } else {
                absGlobal{|ecbMap[pevent].edata := absmbox(msg_in)|}
            };
        default: absGlobal;
    }
}

query OSMboxPost2_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| == 0;
    assumes absGlobal2 == OSMboxPostAbs2(absGlobal, pevent, msg);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSMboxPost2_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSMboxPostAbs2(absGlobal, pevent, msg);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSMboxPost2_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSMboxPostAbs2(absGlobal, pevent, msg);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSMboxPost2_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventGrp == 0;
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_MBOX;
    assumes global2 == OSMboxPost(global, pevent, msg);
    assumes absGlobal2 == OSMboxPostAbs2(absGlobal, pevent, msg);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

/*
 * Helper function: removing an element from the circular queue.
 * This is used in both QAccept and QPend.
 */
function QRemoveElement(OS_Q q1) -> Prod<OS_Q, addrval> {
    pair(OS_Q{{
            OSQIn: q1.OSQIn,
            OSQOut: if (q1.OSQOut + 1 == |q1.OSQData|) {
                0
            } else {
                q1.OSQOut + 1
            },
            OSQEntries: q1.OSQEntries - 1,
            OSQData: q1.OSQData
         }},
         q1.OSQData[q1.OSQOut]
    )
}

/*
 * As a sanity check, we prove QRemoveElement satisfies the right properties.
 */
query QRemoveElement_MatchLHMsgList {
    fixes q1: OS_Q;
    fixes q2: OS_Q;
    fixes msgl: Seq<addrval>;
    fixes ret: Prod<OS_Q, addrval>;
    assumes q1.OSQEntries > 0;
    assumes MatchLHMsgList(q1, msgl);
    assumes ret == QRemoveElement(q1);
    shows MatchLHMsgList(ret.fst, seq_remove(0, msgl)) && ret.snd == msgl[0]
    proof { seq_auto }
}

function OSQAccept(Global global, address pevent) -> Prod<Global, addrval> {
    let q = get(pevent, global.events).OSQueue.val in
        if (q.OSQEntries > 0) {
            let ret = QRemoveElement(q) in
            let global2 = global{|events[pevent].OSQueue := some(ret.fst)|} in
                pair(global2, ret.snd)
            end
            end
        } else {
            pair(global, Vnull)
        }
    end
}

function OSQAcceptAbs(AbsGlobal absGlobal, address pevent) -> Prod<AbsGlobal, addrval> {
    switch (get(pevent, absGlobal.ecbMap)) {
        case AbsECB{{edata: absmsgq(msgl, qsize), wset: wset}}:
            if (|msgl| == 0) {
                pair(absGlobal, Vnull)
            } else {
                let absGlobal2 = absGlobal{|ecbMap[pevent] :=
                    AbsECB{{edata: absmsgq(seq_remove(0, msgl), qsize), wset: wset}}|} in
                    pair(absGlobal2, msgl[0])
                end
            };
        default:
            pair(absGlobal, Vnull);
    }
}

query OSQAccept_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    fixes msg: addrval;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes pair(absGlobal2, msg) == OSQAcceptAbs(absGlobal, pevent);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSQAccept_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    fixes msg: addrval;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes pair(absGlobal2, msg) == OSQAcceptAbs(absGlobal, pevent);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSQAccept_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    fixes msg: addrval;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes pair(absGlobal2, msg) == OSQAcceptAbs(absGlobal, pevent);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSQAccept_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    fixes absMsg: addrval;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_Q;
    assumes pair(global2, msg) == OSQAccept(global, pevent);
    assumes pair(absGlobal2, absMsg) == OSQAcceptAbs(absGlobal, pevent);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap)) &&
          msg == absMsg
    proof { seq_auto }
}

/*
 * First part of OSQPend (before OSSched).
 *
 * Assume pevent is in global.events and the event type is OS_EVENT_TYPE_Q.
 */
function OSQPend1(Global global, address pevent, int16u timeout) -> Global {
    let q = get(pevent, global.events).OSQueue.val in
        if (q.OSQEntries > 0) {
            let ret = QRemoveElement(q) in
            let global2 = global{|events[pevent].OSQueue := some(ret.fst)|} in
                global2{|OSTCBPrioTbl[global.OSPrioCur].OSTCBMsg := ret.snd|}
            end
            end
        } else {
            let global2 = global{|OSTCBPrioTbl[global.OSPrioCur].OSTCBStat :=
                                get(global.OSPrioCur, global.OSTCBPrioTbl).OSTCBStat | OS_STAT_Q|} in
            let global3 = global2{|OSTCBPrioTbl[global.OSPrioCur].OSTCBDly := timeout|} in
                OS_EventTaskWait(global3, pevent)
            end
            end
        }
    end
}

function OSQPend2(Global global, address pevent) -> Global {
    if (get(global.OSPrioCur, global.OSTCBPrioTbl).OSTCBMsg == Vnull) {
        OS_EventTO(global, pevent)
    } else {
        let global2 = global{|OSTCBPrioTbl[global.OSPrioCur].OSTCBMsg := Vnull|} in
        let global3 = global2{|OSTCBPrioTbl[global.OSPrioCur].OSTCBStat := OS_STAT_RDY|} in
            global3{|OSTCBPrioTbl[global.OSPrioCur].OSTCBEventPtr := Vnull|}
        end
        end
    }
}

/*
 * Abstract version of OSQPend1.
 *
 * Assume pevent is in absGlobal.ecbMap.
 */
function OSQPendAbs1(AbsGlobal absGlobal, address pevent, int16u timeout) -> AbsGlobal {
    switch (get(pevent, absGlobal.ecbMap)) {
        case AbsECB{{edata: absmsgq(msgl, qsize), wset: wset}}:
            if (|msgl| == 0) {
                let absGlobal2 = absGlobal{|ecbMap[pevent] :=
                    AbsECB{{edata: absmsgq(msgl, qsize),
                            wset: seq_cons(absGlobal.curTask, get(pevent, absGlobal.ecbMap).wset)}}|} in
                    absGlobal2{|tcbMap[absGlobal.curTask].stat := wait(os_stat_q(pevent), timeout)|}
                end
            } else {
                let absGlobal2 = absGlobal{|ecbMap[pevent].edata := absmsgq(seq_remove(0, msgl), qsize)|} in
                    absGlobal2{|tcbMap[absGlobal.curTask].msg := msgl[0]|}
                end
            };
        default:
            absGlobal;
    }
}

query OSQPend1_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes timeout: int16u;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSQPendAbs1(absGlobal, pevent, timeout);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSQPend1_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes timeout: int16u;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSQPendAbs1(absGlobal, pevent, timeout);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSQPend1_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes timeout: int16u;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSQPendAbs1(absGlobal, pevent, timeout);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSQPend1_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes timeout: int16u;
    fixes pevent: address;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_Q;
    assumes global2 == OSQPend1(global, pevent, timeout);
    assumes absGlobal2 == OSQPendAbs1(absGlobal, pevent, timeout);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

/*
 * Abstract version of OSQPend2.
 */
function OSQPendAbs2(AbsGlobal absGlobal, address pevent) -> AbsGlobal {
    let absGlobal2 = absGlobal{|tcbMap[absGlobal.curTask].msg := Vnull|} in
        absGlobal2{|tcbMap[absGlobal.curTask].stat := rdy|}
    end
}

query OSQPend2_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSQPendAbs2(absGlobal, pevent);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSQPend2_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSQPendAbs2(absGlobal, pevent);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSQPend2_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSQPendAbs2(absGlobal, pevent);
    assumes RH_CurTask_Ready(absGlobal);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSQPend2_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes pevent: address;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_Q;
    assumes global2 == OSQPend2(global, pevent);
    assumes absGlobal2 == OSQPendAbs2(absGlobal, pevent);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

/*
 * Helper function: adding an element to the circular queue.
 * This is used in QPost.
 */
function QAddElement(OS_Q q1, addrval msg) -> OS_Q {
    let qin = q1.OSQIn in
    let qsize = |q1.OSQData| in
        OS_Q{{
            OSQIn: if (qin + 1 == qsize) {
                0
            } else {
                qin + 1
            },
            OSQOut: q1.OSQOut,
            OSQEntries: q1.OSQEntries + 1,
            OSQData: seq_update(qin, msg, q1.OSQData)
        }}
    end
    end
}

/*
 * As a sanity check, we prove QAddElement satisfies the right properties.
 */
query QAddElement_MatchLHMsgList {
    fixes q1: OS_Q;
    fixes q2: OS_Q;
    fixes msgl: Seq<addrval>;
    fixes msg: addrval;
    fixes qsize: int;
    assumes qsize == |q1.OSQData|;
    assumes q1.OSQEntries < qsize;
    assumes MatchLHMsgList(q1, msgl);
    assumes q2 == QAddElement(q1, msg);
    shows MatchLHMsgList(q2, msgl ++ seq_repeat(msg, 1))
    proof { seq_auto }
}

/*
 * Part of OSQPost before OS_Sched.
 */
function OSQPost(Global global, address pevent, addrval msg) -> Global {
    let event = get(pevent, global.events) in
        if (event.OSEventGrp != 0) {
            OS_EventTaskRdy(global, pevent, msg, OS_STAT_Q)
        } else {
            let q1 = event.OSQueue.val in
            let qsize = |q1.OSQData| in
                if (q1.OSQEntries >= qsize) {
                    global
                } else {
                    let q2 = QAddElement(q1, msg) in
                        global{|events[pevent].OSQueue := some(q2)|}
                    end
                }
            end
            end
        }
    end
}

/*
 * Abstract version of OSQPost.
 */
function OSQPostAbsHelper(AbsGlobal absGlobal, address pevent, int highPrioId, addrval msg) -> AbsGlobal {
    let highPrio = get(pevent, absGlobal.ecbMap).wset[highPrioId] in
    let absGlobal2 = absGlobal{|ecbMap[pevent].wset :=
            seq_remove(highPrioId, get(pevent, absGlobal.ecbMap).wset)|} in
    let absGlobal3 = absGlobal2{|tcbMap[highPrio].stat := rdy|} in
        absGlobal3{|tcbMap[highPrio].msg := msg|}
    end
    end
    end
}

predicate OSQPostAbs1(AbsGlobal absGlobal, AbsGlobal absGlobal2, address pevent, addrval msg) {
    exists (int highPrioId) {
        highPrioIdInWset(get(pevent, absGlobal.ecbMap).wset, highPrioId) &&
        absGlobal2 == OSQPostAbsHelper(absGlobal, pevent, highPrioId, msg)
    }
}

query OSQPost1_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    fixes msg: addrval;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| > 0;
    assumes OSQPostAbs1(absGlobal, absGlobal2, pevent, msg);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSQPost1_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    fixes msg: addrval;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| > 0;
    assumes OSQPostAbs1(absGlobal, absGlobal2, pevent, msg);
    assumes event_wset_unique(absGlobal);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSQPost1_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes absGlobal2: AbsGlobal;
    fixes msg: addrval;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| > 0;
    assumes OSQPostAbs1(absGlobal, absGlobal2, pevent, msg);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSQPost1_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventGrp != 0;
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_MBOX;
    assumes global2 == OSMboxPost(global, pevent, msg);
    assumes OSQPostAbs1(absGlobal, absGlobal2, pevent, msg);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}

function OSQPostAbs2(AbsGlobal absGlobal, address pevent, addrval msg) -> AbsGlobal {
    switch (get(pevent, absGlobal.ecbMap)) {
        case AbsECB{{edata: absmsgq(msgl, qsize), wset: wset}}:
            if (|msgl| >= qsize) {
                absGlobal
            } else {
                absGlobal{|ecbMap[pevent].edata := absmsgq(msgl ++ seq_repeat(msg, 1), qsize)|}
            };
        default: absGlobal;
    }
}

query OSQPost2_RH_ECB_P {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes |get(pevent, absGlobal.ecbMap).wset| == 0;
    assumes absGlobal2 == OSQPostAbs2(absGlobal, pevent, msg);
    assumes RH_ECB_P_All(absGlobal);
    shows RH_ECB_P_All(absGlobal2)
    proof { seq_auto }
}

query OSQPost2_RH_TCBList_ECBList_P1 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSQPostAbs2(absGlobal, pevent, msg);
    assumes RH_TCBList_ECBList_P1(absGlobal);
    shows RH_TCBList_ECBList_P1(absGlobal2)
    proof { seq_auto }
}

query OSQPost2_RH_TCBList_ECBList_P2 {
    fixes absGlobal: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    fixes absGlobal2: AbsGlobal;
    assumes indom(pevent, absGlobal.ecbMap);
    assumes absGlobal2 == OSQPostAbs2(absGlobal, pevent, msg);
    assumes RH_TCBList_ECBList_P2(absGlobal);
    shows RH_TCBList_ECBList_P2(absGlobal2)
    proof { seq_auto }
}

query OSQPost2_RLH_ECBData_P {
    fixes global: Global;
    fixes absGlobal: AbsGlobal;
    fixes global2: Global;
    fixes absGlobal2: AbsGlobal;
    fixes pevent: address;
    fixes msg: addrval;
    assumes indom(pevent, global.events);
    assumes get(pevent, global.events).OSEventGrp == 0;
    assumes get(pevent, global.events).OSEventType == OS_EVENT_TYPE_Q;
    assumes global2 == OSQPost(global, pevent, msg);
    assumes absGlobal2 == OSQPostAbs2(absGlobal, pevent, msg);
    assumes RLH_ECBData_P(get(pevent, global.events), get(pevent, absGlobal.ecbMap));
    shows RLH_ECBData_P(get(pevent, global2.events), get(pevent, absGlobal2.ecbMap))
    proof { seq_auto }
}
