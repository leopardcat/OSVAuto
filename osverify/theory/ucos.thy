imports basic
imports ucosData

predicate RL_TCBblk_P (TCB tcb) {
    0 <= tcb.prio && tcb.prio < 64 &&
    tcb.prio & 7 == tcb.x &&
    tcb.prio >> 3 == tcb.y &&
    1 << tcb.x == tcb.bitx &&
    1 << tcb.y == tcb.bity &&
    (tcb.stat == OS_STAT_RDY || tcb.stat == OS_STAT_SUSPEND ||
        tcb.stat == OS_STAT_SEM || tcb.stat == OS_STAT_Q ||
        tcb.stat == OS_STAT_MBOX || tcb.stat == OS_STAT_MUTEX ||
        tcb.stat == OS_STAT_SEM | OS_STAT_SUSPEND ||
        tcb.stat == OS_STAT_Q | OS_STAT_SUSPEND ||
        tcb.stat == OS_STAT_MBOX | OS_STAT_SUSPEND ||
        tcb.stat == OS_STAT_MUTEX | OS_STAT_SUSPEND) &&
    ((tcb.stat == OS_STAT_RDY || tcb.stat == OS_STAT_SUSPEND) -> tcb.eptr == Vnull)
}

predicate prio_in_tbl(int32u prio, int32u[] rtbl) {
    let x = prio & 7 in
        rtbl[prio >> 3] & (1 << x) == 1 << x
    end
}

predicate prio_not_in_tbl(int32u prio, int32u[] rtbl) {
    let x = prio & 7 in
        rtbl[prio >> 3] & (1 << x) == 0
    end
}

// We now write down the refinement relations between high- and
// low-level task information.

// Refinement relation: rdy case

predicate RLH_RdyI_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    prio_in_tbl(tcb.prio, rtbl) ->
    tcb.stat == OS_STAT_RDY && tcb.dly == 0 &&
    abstcb.prio == tcb.prio && abstcb.stat == rdy && abstcb.sus == false
}

predicate RHL_RdyI_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    abstcb.stat == rdy && abstcb.sus == false ->
    prio_in_tbl(tcb.prio, rtbl) && tcb.prio == abstcb.prio &&
    tcb.stat == OS_STAT_RDY && tcb.dly == 0
}

// Refinement relation: wait case

predicate RLH_Wait_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_RDY ->
    tcb.dly > 0 && abstcb.prio == tcb.prio &&
    abstcb.stat == wait(os_stat_time, tcb.dly) && abstcb.sus == false
}

predicate RHL_Wait_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_time, d), sus: false}}:
            prio == tcb.prio && prio_not_in_tbl(prio, rtbl) &&
            d == tcb.dly && d > 0 && tcb.stat == OS_STAT_RDY;
        default: true;
    }
}

// Refinement relation: suspend case

predicate RLH_Suspend_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    (
        prio_not_in_tbl(tcb.prio, rtbl) -> tcb.dly == 0 -> tcb.stat == OS_STAT_SUSPEND ->
        abstcb.prio == tcb.prio && abstcb.stat == rdy && abstcb.sus == true
    )
    &&
    (
        prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_SUSPEND -> tcb.dly > 0 ->
        abstcb.prio == tcb.prio && abstcb.stat == wait(os_stat_time, tcb.dly) && abstcb.sus == true
    )
}

predicate RHL_Suspend_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    (
        abstcb.stat == rdy -> abstcb.sus == true ->
        prio_not_in_tbl(tcb.prio, rtbl) && tcb.prio == abstcb.prio && tcb.dly == 0 && tcb.stat == OS_STAT_SUSPEND
    )
    &&
    (
        switch (abstcb) {
            case AbsTCB{{prio: prio, stat: wait(os_stat_time, d), sus: true}}:
                prio == tcb.prio && prio_not_in_tbl(prio, rtbl) &&
                d == tcb.dly && d > 0 && tcb.stat == OS_STAT_SUSPEND;
            default: true;
        }
    )
}

// Refinement relation: wait for semaphore

predicate RLH_WaitS_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_SEM ->
    switch (tcb.eptr) {
        case Vptr(eid):
            abstcb.prio == tcb.prio && abstcb.stat == wait(os_stat_sem(eid), tcb.dly) &&
            abstcb.sus == false;
        default: true;
    }
}

predicate RHL_WaitS_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_sem(eid), dly), sus: false}}:
            tcb.prio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.eptr == Vptr(eid) && tcb.stat == OS_STAT_SEM;
        default: true;
    }
}

// Refinement relation: wait for semaphore and suspend

predicate RLH_WaitS_Suspend_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_SEM | OS_STAT_SUSPEND ->
    switch (tcb.eptr) {
        case Vptr(eid):
            abstcb.prio == tcb.prio && abstcb.stat == wait(os_stat_sem(eid), tcb.dly) &&
            abstcb.sus == true;
        default: true;
    }
}

predicate RHL_WaitS_Suspend_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_sem(eid), dly), sus: true}}:
            tcb.prio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.eptr == Vptr(eid) && tcb.stat == OS_STAT_SEM | OS_STAT_SUSPEND;
        default: true;
    }
}

// Refinement relation: wait for queue

predicate RLH_WaitQ_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_Q ->
    switch (tcb.eptr) {
        case Vptr(eid):
            abstcb.prio == tcb.prio && abstcb.stat == wait(os_stat_q(eid), tcb.dly) &&
            abstcb.sus == false;
        default: true;
    }
}

predicate RHL_WaitQ_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_q(eid), dly), sus: false}}:
            tcb.prio == prio && prio_not_in_tbl(prio, rtbl) && 
            tcb.eptr == Vptr(eid) && tcb.stat == OS_STAT_Q;
        default: true;
    }
}

// Refinement relation: wait for queue and suspend

predicate RLH_WaitQ_Suspend_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_Q | OS_STAT_SUSPEND ->
    switch (tcb.eptr) {
        case Vptr(eid):
            abstcb.prio == tcb.prio && abstcb.stat == wait(os_stat_q(eid), tcb.dly) &&
            abstcb.sus == true;
        default: true;
    }
}

predicate RHL_WaitQ_Suspend_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_q(eid), dly), sus: true}}:
            tcb.prio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.eptr == Vptr(eid) && tcb.stat == OS_STAT_Q | OS_STAT_SUSPEND;
        default: true;
    }
}

// Refinement relation: wait for mailbox

predicate RLH_WaitMB_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_MBOX ->
    switch (tcb.eptr) {
        case Vptr(eid):
            abstcb.prio == tcb.prio && abstcb.stat == wait(os_stat_mbox(eid), tcb.dly) &&
            abstcb.sus == false;
        default: true;
    }
}

predicate RHL_WaitMB_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_mbox(eid), dly), sus: false}}:
            tcb.prio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.eptr == Vptr(eid) && tcb.stat == OS_STAT_MBOX;
        default: true;
    }
}

// Refinement relation: wait for mailbox and suspend

predicate RLH_WaitMB_Suspend_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_MBOX | OS_STAT_SUSPEND ->
    switch (tcb.eptr) {
        case Vptr(eid):
            abstcb.prio == tcb.prio && abstcb.stat == wait(os_stat_mbox(eid), tcb.dly) &&
            abstcb.sus == true;
        default: true;
    }
}

predicate RHL_WaitMB_Suspend_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_mbox(eid), dly), sus: true}}:
            tcb.prio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.eptr == Vptr(eid) && tcb.stat == OS_STAT_MBOX | OS_STAT_SUSPEND;
        default: true;
    }
}

// Refinement relation: wait for mutex

predicate RLH_WaitMS_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_MUTEX ->
    switch (tcb.eptr) {
        case Vptr(eid):
            abstcb.prio == tcb.prio && abstcb.stat == wait(os_stat_mutexsem(eid), tcb.dly) &&
            abstcb.sus == false;
        default: true;
    }
}

predicate RHL_WaitMS_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_mutexsem(eid), dly), sus: false}}:
            tcb.prio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.eptr == Vptr(eid) && tcb.stat == OS_STAT_MUTEX;
        default: true;
    }
}

// Refinement relation: wait for mutex and suspend

predicate RLH_WaitMS_Suspend_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    prio_not_in_tbl(tcb.prio, rtbl) -> tcb.stat == OS_STAT_MUTEX | OS_STAT_SUSPEND ->
    switch (tcb.eptr) {
        case Vptr(eid):
            abstcb.prio == tcb.prio && abstcb.stat == wait(os_stat_mutexsem(eid), tcb.dly) &&
            abstcb.sus == true;
        default: true;
    }
}

predicate RHL_WaitMS_Suspend_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    switch (abstcb) {
        case AbsTCB{{prio: prio, stat: wait(os_stat_mutexsem(eid), dly), sus: true}}:
            tcb.prio == prio && prio_not_in_tbl(prio, rtbl) &&
            tcb.eptr == Vptr(eid) && tcb.stat == OS_STAT_MUTEX | OS_STAT_SUSPEND;
        default: true;
    }
}

// Collection of all low-to-high relations: wait for event

predicate RLH_TCB_Status_Wait_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
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

// Collection of all high-to-low relations: wait for event

predicate RHL_TCB_Status_Wait_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
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

// All refinement relations for task information

predicate R_TCB_Status_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    RLH_RdyI_P(tcb, rtbl, abstcb) &&
    RHL_RdyI_P(tcb, rtbl, abstcb) &&
    RLH_Suspend_P(tcb, rtbl, abstcb) &&
    RHL_Suspend_P(tcb, rtbl, abstcb) &&
    RLH_TCB_Status_Wait_P(tcb, rtbl, abstcb) &&
    RHL_TCB_Status_Wait_P(tcb, rtbl, abstcb)
}

/*
 * We now write down the refinement relations between high- and
 * low-level event information.
 */

/*
 * Same as prio_in_tbl?
 */
predicate PrioWaitInQ(int32u prio, int32u[] etbl) {
    let x = prio & 7 in 
        let y = prio >> 3 in 
            etbl[y] & (1 << x) == 1 << x
        end
    end
}

/*
 * Low-to-high relation, queue case.
 *
 * For each event control block of queue type, for each priority in
 * the priority table of the event, the priority exists in tcbls, and
 * the corresponding task has status of waiting for the same event.
 */
predicate RLH_ECB_ETbl_Q_P(addrval eid, EventCtr ecb, TCBMap tcbls) {
    forall (int32u prio in range(0, 64)) {
        PrioWaitInQ(prio, ecb.etbl) ->
        ecb.OSEventType == OS_EVENT_TYPE_Q ->
        exists (addrval tid in tcbls) {
            get(tid, tcbls).prio == prio &&
            switch (get(tid, tcbls).stat) {
                case wait(os_stat_q(eid2), _):
                    eid2 == eid;
                default: false;
            }
        }
    }
}

/*
 * High-to-low relation, queue case.
 *
 * For each task in tcbls, if the task is waiting for queue with the
 * given eid, then the task exists in the priority table of the event,
 * and the event type is queue.
 */
predicate RHL_ECB_ETbl_Q_P(addrval eid, EventCtr ecb, TCBMap tcbls) {
    forall (addrval tid in tcbls) {
        switch (get(tid, tcbls)) {
            case AbsTCB{{prio: prio, stat: wait(os_stat_q(eid2), _)}}:
                eid2 == eid ->
                0 <= prio && prio < 64 &&
                PrioWaitInQ(prio, ecb.etbl) &&
                ecb.OSEventType == OS_EVENT_TYPE_Q;
            default: true;
        }
    }
}

/*
 * Low-to-high relation, semaphore case.
 *
 * For each event control block of semaphore type, for each priority in
 * the priority table of the event, the priority exists in tcbls, and
 * the corresponding task has the status of waiting for the same event.
 */
predicate RLH_ECB_ETbl_SEM_P(addrval eid, EventCtr ecb, TCBMap tcbls) {
    forall (int32u prio in range(0, 64)) {
        PrioWaitInQ(prio, ecb.etbl) -> 
        ecb.OSEventType == OS_EVENT_TYPE_SEM ->
        exists (addrval tid in tcbls) {
            get(tid, tcbls).prio == prio &&
            switch (get(tid, tcbls).stat) {
                case wait(os_stat_sem(eid2), _):
                    eid2 == eid;
                default: false;
            }
        }
    }
}

/*
 * High-to-low relation, semaphore case.
 *
 * For each task in tcbls, if the task is waiting for semaphore wit the
 * given eid, then the task exists in the priority table of the event,
 * and the event type is semaphore.
 */
predicate RHL_ECB_ETbl_SEM_P(addrval eid, EventCtr ecb, TCBMap tcbls) {
    forall (addrval tid in tcbls) {
        switch (get(tid, tcbls)) {
            case AbsTCB{{prio: prio, stat: wait(os_stat_sem(eid2), _)}}:
                eid2 == eid ->
                0 <= prio && prio < 64 &&
                PrioWaitInQ(prio, ecb.etbl) &&
                ecb.OSEventType == OS_EVENT_TYPE_SEM;
            default: true;
        }
    }
}

/*
 * Low-to-high relation, mailbox case.
 *
 * For each event control block of mailbox type, for each priority in
 * the priority queue of the event, the priority exists in tcbls, and
 * the corresponding task has the status of waiting for the same event.
 */
predicate RLH_ECB_ETbl_MBOX_P(addrval eid, EventCtr ecb, TCBMap tcbls) {
    forall (int32u prio in range(0, 64)) {
        PrioWaitInQ(prio, ecb.etbl) -> 
        ecb.OSEventType == OS_EVENT_TYPE_MBOX ->
        exists (addrval tid in tcbls) {
            get(tid, tcbls).prio == prio &&
            switch (get(tid, tcbls).stat) {
                case wait(os_stat_mbox(eid2), _):
                    eid2 == eid;
                default: false;
            }
        }
    }
}

/*
 * High-to-low relation, mailbox case.
 *
 * For each task in tcbls, if the task is waiting for mailbox with the
 * given eid, then the task exists in the priority table of the event,
 * and the event type is mailbox.
 */
predicate RHL_ECB_ETbl_MBOX_P(addrval eid, EventCtr ecb, TCBMap tcbls) {
    forall (addrval tid in tcbls) {
        switch (get(tid, tcbls)) {
            case AbsTCB{{prio: prio, stat: wait(os_stat_mbox(eid2), _)}}:
                eid2 == eid ->
                0 <= prio && prio < 64 &&
                PrioWaitInQ(prio, ecb.etbl) &&
                ecb.OSEventType == OS_EVENT_TYPE_MBOX;
            default: true;
        }
    }
}

/*
 * Low-to-high relation, mutex case.
 *
 * For each event control block of mutex type, for each priority in
 * the priority table of the event, the priority exists in tcbls, and
 * the corresponding task has the status of waiting for the same event.
 */
predicate RLH_ECB_ETbl_MUTEX_P(addrval eid, EventCtr ecb, TCBMap tcbls) {
    forall (int32u prio in range(0, 64)) {
        PrioWaitInQ(prio, ecb.etbl) -> 
        ecb.OSEventType == OS_EVENT_TYPE_MUTEX ->
        exists (addrval tid in tcbls) {
            get(tid, tcbls).prio == prio &&
            switch (get(tid, tcbls).stat) {
                case wait(os_stat_mutexsem(eid2), _):
                    eid2 == eid;
                default: false;
            }
        }
    }
}

/*
 * High-to-low relation, mutex case.
 *
 * For each task in tcbls, if the task is waiting for mutex with the
 * given eid, then the task exists in the priority table of the event,
 * and the event type is mutex.
 */
predicate RHL_ECB_ETbl_MUTEX_P(addrval eid, EventCtr ecb, TCBMap tcbls) {
    forall (addrval tid in tcbls) {
        switch (get(tid, tcbls)) {
            case AbsTCB{{prio: prio, stat: wait(os_stat_mutexsem(eid2), _)}}:
                eid2 == eid ->
                0 <= prio && prio < 64 &&
                PrioWaitInQ(prio, ecb.etbl) &&
                ecb.OSEventType == OS_EVENT_TYPE_MUTEX;
            default: true;
        }
    }
}

/*
 * Low-to-high relations: event control block vs. tcbls.
 */
predicate RLH_ECB_ETbl_P(addrval eid, EventCtr ecb, TCBMap tcbls) {
    RLH_ECB_ETbl_Q_P(eid, ecb, tcbls) &&
    RLH_ECB_ETbl_SEM_P(eid, ecb, tcbls) &&
    RLH_ECB_ETbl_MBOX_P(eid, ecb, tcbls) &&
    RLH_ECB_ETbl_MUTEX_P(eid, ecb, tcbls) 
}

/*
 * High-to-low relations: event control block vs. tcbls.
 */
predicate RHL_ECB_ETbl_P(addrval eid, EventCtr ecb, TCBMap tcbls) {
    RHL_ECB_ETbl_Q_P(eid, ecb, tcbls) &&
    RHL_ECB_ETbl_SEM_P(eid, ecb, tcbls) &&
    RHL_ECB_ETbl_MBOX_P(eid, ecb, tcbls) &&
    RHL_ECB_ETbl_MUTEX_P(eid, ecb, tcbls) 
}

/*
 * Invariant for OSEvent.
 *
 * - OSEventType is one of four possible choices.
 */
predicate Event_Type_P(EventCtr ecb) {
    ecb.OSEventType == OS_EVENT_TYPE_Q ||
    ecb.OSEventType == OS_EVENT_TYPE_SEM ||
    ecb.OSEventType == OS_EVENT_TYPE_MBOX ||
    ecb.OSEventType == OS_EVENT_TYPE_MUTEX
}

/*
 * All relations and invariants for event control block.
 */
predicate R_ECB_ETbl_P(addrval eid, EventCtr ecb, TCBMap tcbls){
    RLH_ECB_ETbl_P(eid, ecb, tcbls) &&
    RHL_ECB_ETbl_P(eid, ecb, tcbls) &&
    Event_Type_P(ecb)
}

/*
 * All refinement relations and invariants for abstract and concrete
 * task control blocks.
 */
predicate TCBNode_P(TCB tcb, int32u[] rtbl, AbsTCB abstcb) {
    tcb.msg == abstcb.msg &&
    tcb.prio == abstcb.prio &&
    RL_TCBblk_P(tcb) &&
    R_TCB_Status_P(tcb, rtbl, abstcb)
}

/*
 * Refinement relations between data structures for all abstract and
 * concrete task control blocks.
 *
 * - tcbList is the linked list of concrete task control blocks, with v
 *   being the head pointer.
 * - tcbls is the map of abstract task control blocks. It is formed by
 *   adding tid/abstcb pairs one at a time in the definition of TCBList_P. 
 */
predicate TCBList_P(val v, TCBList tcbList, int32u[] rtbl, TCBMap tcbls) {
    switch (tcbList) {
        case nil: isEmpty(tcbls);
        case cons(tcb, tcbList2):
            switch (v) {
                case Vptr(tid):
                    exists (AbsTCB abstcb, TCBMap tcbls2) {
                        TCBNode_P(tcb, rtbl, abstcb) &&
                        TCBList_P(tcb.next, tcbList2, rtbl, tcbls2) &&
                        join(tid, abstcb, tcbls2, tcbls)
                    };
                default: false;
            };
    }
}

// Properties of PrioTbl, comes from os_inv.v and abs_op.v:

/*
 * There are no duplicate priorities in tcbls.
 */
predicate R_Prio_No_Dup(TCBMap tcbls) {
    forall (addrval tid1 in tcbls) {
        forall (addrval tid2 in tcbls) {
            tid1 != tid2 ->
            get(tid1, tcbls).prio != get(tid2, tcbls).prio
        }
    }
}

/*
 * Invariant relating tcbls and ptbl (array of pointers to TCB).
 *
 * 1. For each priority in range, if the value in ptbl is Vptr(tid)
 *    where tid is not vhold, then tid is in tcbls with the same priority.
 * 2. For each task in tcbls, the corresponding entry in ptbl has the
 *    right value that is not vhold.
 * 3. There are no duplicate priorities in tcbls.
 */
predicate R_PrioTbl_P(val[] ptbl, TCBMap tcbls, addrval vhold) {
    forall (int32u prio in range(0, 64)) {
        switch (ptbl[prio]) {
            case Vptr(tid):
                tid != vhold ->
                indom(tid, tcbls) && get(tid, tcbls).prio == prio;
            default: true;
        }
    } &&
    forall (addrval tid in tcbls) {
        0 <= get(tid, tcbls).prio && get(tid, tcbls).prio < 64 &&
        switch (ptbl[get(tid, tcbls).prio]) {
            case Vptr(tid2):
                tid == tid2 && tid != vhold;
            default: false;
        }
    } &&
    R_Prio_No_Dup(tcbls)
}

/*
 * Invariant relating rtbl and ptbl.
 *
 * For each priority that is in rtbl, the corresponding entry in ptbl
 * is in the form Vptr(tid), where tid is not vhold.
 */
predicate RL_RTbl_PrioTbl_P(int32u[] rtbl, val[] ptbl, addrval vhold){
    forall (int32u prio in range(0, 64)) {
        prio_in_tbl(prio, rtbl) ->
        switch (ptbl[prio]) {
            case Vptr(tid):
                tid != vhold;
            default: false;
        }
    }
}

/*
 * This lemma appears in OSMutexPostPart30. It states if ptbl is vhold at some
 * priority, then that priority can be added into tcbls, without violating
 * no-duplicate condition.
 */
query mutex_post_nodup {
    fixes ptbl : val[];
    fixes tcbls1 : TCBMap;
    fixes tcbls2 : TCBMap;
    fixes vhold : addrval;
    fixes tid : addrval;
    fixes block : int32u;
    fixes abstcb : AbsTCB;
    assumes R_PrioTbl_P(ptbl, tcbls1, vhold);
    assumes ptbl[abstcb.prio] == Vptr(vhold);
    assumes indom(tid, tcbls1);
    assumes mapUpdate(tid, abstcb, tcbls1, tcbls2);
    shows R_Prio_No_Dup(tcbls2)
    proof { auto }
}

/*
 * No waiting events in tcbls is present in ecbls.
 */
predicate ecb_no_exists_tcb(ECBMap ecbls, TCBMap tcbls) {
    forall (addrval tid in tcbls) {
        switch (get(tid, tcbls)) {
            case AbsTCB{{stat: st}}:
                switch (st) {
                    case wait(os_stat_sem(eid), _):
                        !indom(eid, ecbls);
                    case wait(os_stat_q(eid), _):
                        !indom(eid, ecbls);
                    case wait(os_stat_mbox(eid), _):
                        !indom(eid, ecbls);
                    case wait(os_stat_mutexsem(eid), _):
                        !indom(eid, ecbls);
                    default: true;
                };
        }
    }
}

// ucos_common.v

predicate prio_neq_cur(TCBMap tcbls, addrval curtid, int32u curprio) {
    forall (addrval tid in tcbls) {
        tid != curtid -> 
        get(tid, tcbls).prio != curprio
    }
}

/*
 * Properties of the abstract ECB:
 *
 * For semaphores, if count is positive, then the list of waiting tasks
 * empty. The converse also holds.
 *
 * For message queues, if the message list is nonempty, then the list of
 * waiting tasks is empty. The converse also holds.
 *
 * For mailboxes, if the message is not null, then the list of waiting
 * tasks is empty. The converse also holds.
 *
 * For mutexes, if there is no owner, then the list of waiting tasks is
 * empty. Otherwise, the priority of the mutex is less than the original
 * priority of owner (note less means higher priority), and the original
 * priority of owner is less than 64. Furthermore, if the set of waiting
 * tasks is nonempty, then there must be an owner. Finally, the priority
 * of the mutex is always less than 64.
 *
 */
predicate RH_ECB_P(AbsECB absecb) {
    switch (absecb.edata) {
        case abssem(count): 
            (count > 0 -> absecb.wset == nil) &&
            (absecb.wset != nil -> count == 0);
        case absmsgq(msgl, qsize):
            (msgl != nil -> absecb.wset == nil) &&
            (absecb.wset != nil -> msgl == nil);
        case absmbox(msg):
            (msg != Vnull -> absecb.wset == nil) &&
            (absecb.wset != nil -> msg == Vnull);
        case absmutexsem(prio, owner):
            switch (owner) {
                case none: absecb.wset == nil;
                case some(own): prio < own.oprio && own.oprio < 64;
                default: false;
            } &&
            (absecb.wset != nil -> owner != none) &&
            prio < 64;
        default: false;
    }
}

// Distance between two addresses
function distance(addrval startpos, addrval endpos) -> nat {
    nat((endpos.offset - startpos.offset) / 4)
}

// Value is pointer if it is of type Vnull or Vptr
predicate isptr(val v) {
    switch (v) {
        case Vnull: true;
        case Vptr(p): true;
        default: false;
    }
}

// List of values are all pointers
predicate isptr_list(List<val> vl) {
    switch (vl) {
        case nil: true;
        case cons(v, vl2): isptr(v) && isptr_list(vl2);
        default: false;
    }
}

/*
 * Matching between low-level and high-level message lists
 *
 * Here d1 and d2 are indices of qin and qout, respectively.
 * If d2 > d1, then the message list is the segment between d1 and d2.
 * If d2 < d1, then the message list is the segment from d1 to end, followed
 *             by the segment from beginning to d2.
 * If d2 == d1, then there are two cases:
 *   1. if the number of entries is zero, then the message list is nil.
 *   2. if the number of entries is full, then the message list is the segment
 *      from d1 to end, followed by the segment from beginning to d2.
 * Finally, the message list are all pointers.
 */
predicate MatchLHMsgList(osqueue osq, List<val> msgtbl, List<val> msgl) {
    let d1 = distance(osq.qstart, osq.qin) in
    let d2 = distance(osq.qstart, osq.qout) in
        (d2 > d1 -> segment(d1, d2, msgtbl) == msgl) &&
        (d2 < d1 -> append(segment(d1, nat(osq.qsize), msgtbl),
                            segment(0, d2, msgtbl)) == msgl) &&
        (d2 == d1 ->
            (osq.qentries == 0 && msgl == nil) ||
            (osq.qentries == osq.qsize && append(segment(d1, nat(osq.qsize), msgtbl),
                                                segment(0, d2, msgtbl)) == msgl))
    end end
    &&
    isptr_list(msgl)
}

// Matching of message length
predicate MatchLHMsgLength(osqueue osq, List<val> msgl) {
    nat(osq.qentries) == length(msgl)
}

// Matching of message size
predicate MatchLHMsgSize(osqueue osq, int32u qmaxlen) {
    osq.qsize == qmaxlen
}

/*
 * Matching between low-level and high-level mutex information
 *
 * x is a 16-bit integer, whose higher 8 bit corresponds to prio (priority)
 * of mutex, and the lower 8 bit is either 255 (not owned) or original
 * priority of the owning task.
 *
 * y is either Vnull (not owned) or corresponds to the owning task.
 */
predicate MatchMutexSem(val x, val y, int32u prio, Option<owner> owner) {
    switch (x) {
        case Vint32(v):
            v <= 65535 &&
            prio == v >> 8 &&
            (v & 255 == 255 -> owner == none && y == Vnull) &&
            (v & 255 != 255 ->
                switch (y) {
                    case Vptr(tid): owner == some(owner{{tid: tid, oprio: v & 255}});
                    default: false;
                });
        default: false;
    }
}

/*
 * Matching between low-level and high-level event data
 */
predicate RLH_ECBData_P(leventdata lecb, AbsECB hecb) {
    switch (lecb) {
        case DMsgQ(a, osq, osqblk, msgtbl):
            switch (hecb.edata) {
                case absmsgq(msgl, qmaxlen):
                    MatchLHMsgList(osq, msgtbl, msgl) &&
                    MatchLHMsgLength(osq, msgl) &&
                    MatchLHMsgSize(osq, qmaxlen) && RH_ECB_P(hecb);
                default: false;
            };
        case DSem(n1):
            switch (hecb.edata) {
                case abssem(n2): n1 == n2 && RH_ECB_P(hecb);
                default: false;
            };
        case DMbox(a):
            switch (hecb.edata) {
                case absmbox(b): a == b && RH_ECB_P(hecb);
                default: false;
            };
        case DMutex(x, y):
            switch (hecb.edata) {
                case absmutexsem(pr, owner):
                    MatchMutexSem(x, y, pr, owner) && RH_ECB_P(hecb);
                default: false;
            };
        default: false;
    }
}

// Definition of ECBList_P, of which ecbList corresopnding to l and edls corresopnding to ecbls in the Coq version
predicate ECBList_P(val v, val tl, List<EventCtr> ecbList, List<leventdata> edls, ECBMap ecbls, TCBMap tcbls) {
    switch(ecbList) {
        case nil:
            edls == nil && isEmpty(ecbls) && v == tl;
        case cons(ecb, ecbList2):
            switch(v) {
                case Vptr(eid):
                    R_ECB_ETbl_P(eid, ecb, tcbls) &&
                    switch(edls){
                        case nil: false;
                        case cons(enode, edls2):
                            exists (AbsECB absmq, ECBMap ecbls2) {
                                RLH_ECBData_P(enode, absmq) &&
                                ECBList_P(ecb.OSEventListPtr, tl, ecbList2, edls2, ecbls2, tcbls) &&
                                join(eid, absmq, ecbls2, ecbls)
                            };
                        default: false;
                    };
                default: false;
            };
        default: false;
    }
}

// Mbox_common.v
// Setting mailbox value to null in both low and high-level data
query RLH_ECBData_p_high_mbox_acpt_hold {
    fixes a : addrval;
    fixes e : eventdata;
    fixes w : List<addrval>;
    assumes RLH_ECBData_P(DMbox(Vptr(a)), AbsECB{{edata: e, wset: w}});
    shows RLH_ECBData_P(DMbox(Vnull),  AbsECB{{edata: absmbox(Vnull), wset: w}})
    proof { auto }
}

// OSMutex_common.v
// Original name: RLH_ECBData_p_high_mbox_acpt_hold
// Setting the owning task of mutex in both low and high-level data
query RLH_ECBData_p_high_mutex_acpt_hold {
    fixes x : int32u;
    fixes i6 : int32u;
    fixes e : eventdata;
    fixes w0 : List<addrval>;
    fixes tid : addrval;
    assumes i6 < 64;
    assumes (x >> 8) < i6;
    assumes RLH_ECBData_P(DMutex(Vint32(x), Vnull), AbsECB{{edata: e, wset: w0}});
    shows RLH_ECBData_P(
        DMutex(Vint32((x & 65280) | i6), Vptr(tid)),
        AbsECB{{edata: absmutexsem(((x & 65280) | i6) >> 8, some(owner{{tid: tid, oprio: i6}})),
                wset: w0}}
    )
    proof { auto }
}

/**************************************
* Relation betwen TCBList and ECBList *
**************************************/

/*
 * Relationship between high-level TCB and ECB, queue case.
 *
 * 1. For each queue eid, if task tid is in the wait-set of the queue,
 *    then the corresponding TCB must be waiting for the same queue.
 * 2. For each task tid, if the task is waiting for queue eid, then
 *    the task must be in the wait-set of the queue.
 */
predicate RH_TCBList_ECBList_Q_P(ECBMap ecbls, TCBMap tcbls) {
    forall (addrval eid in ecbls) {
        switch (get(eid, ecbls)) {
            case AbsECB{{edata: absmsgq(_, _), wset: qwaitset}}:
                forall (addrval tid in qwaitset) {
                    indom(tid, tcbls) &&
                    switch (get(tid, tcbls)) {
                        case AbsTCB{{stat: wait(os_stat_q(eid2), _)}}:
                            eid == eid2;
                        default: false;
                    }
                };
            default: true;
        }
    } &&
    forall (addrval tid in tcbls) {
        switch (get(tid, tcbls)) {
            case AbsTCB{{stat: wait(os_stat_q(eid), _)}}:
                indom(eid, ecbls) &&
                switch (get(eid, ecbls)) {
                    case AbsECB{{edata: absmsgq(_, _), wset: qwaitset}}:
                        inlist(tid, qwaitset);
                    default: false;
                };
            default: true;
        }
    }
}

/*
 * Relationship between high-level TCB and ECB: semaphore case.
 *
 * 1. For each semaphore eid, if a task is in the waiting list of the
 *    semaphore, then the corresopnding TCB must be waiting for the
 *    same semaphore.
 * 2. For each task tid, if the task is waiting for semaphore eid,
 *    then the task is in the waiting list of the semaphore.
 */
predicate RH_TCBList_ECBList_SEM_P(ECBMap ecbls, TCBMap tcbls) {
    forall (addrval eid in ecbls) {
        switch (get(eid, ecbls)) {
            case AbsECB{{edata: abssem(_), wset: wls}}:
                forall (addrval tid in wls) {
                    indom(tid, tcbls) &&
                    switch (get(tid, tcbls)) {
                        case AbsTCB{{stat: wait(os_stat_sem(eid2), _)}}:
                            eid == eid2;
                        default: false;
                    }
                };
            default: true;
        }
    } &&
    forall (addrval tid in tcbls) {
        switch (get(tid, tcbls)) {
            case AbsTCB{{stat: wait(os_stat_sem(eid), _)}}:
                indom(eid, ecbls) &&
                switch (get(eid, ecbls)) {
                    case AbsECB{{edata: abssem(_), wset: wls}}:
                        inlist(tid, wls);
                    default: false;
                };
            default: true;
        }
    }
}

/*
 * Relationship between high-level TCB and ECB: mailbox case.
 *
 * 1. For each mailbox eid, if the task tid is in the waiting list
 *    of the mailbox, then the corresponding TCB of the task is
 *    waiting for the same mailbox.
 * 2. For each task tid, if the task is waiting for mailbox eid,
 *    then the task is in the waiting list of the mailbox.
 */
predicate RH_TCBList_ECBList_MBOX_P(ECBMap ecbls, TCBMap tcbls) {
    forall (addrval eid in ecbls) {
        switch (get(eid, ecbls)) {
            case AbsECB{{edata: absmbox(_), wset: wls}}:
                forall (addrval tid in wls) {
                    indom(tid, tcbls) &&
                    switch (get(tid, tcbls)) {
                        case AbsTCB{{stat: wait(os_stat_mbox(eid2), _)}}:
                            eid == eid2;
                        default: false;
                    }
                };
            default: true;
        }
    } &&
    forall (addrval tid in tcbls) {
        switch (get(tid, tcbls)) {
            case AbsTCB{{stat: wait(os_stat_mbox(eid), _)}}:
                indom(eid, ecbls) &&
                switch (get(eid, ecbls)) {
                    case AbsECB{{edata: absmbox(_), wset: wls}}:
                        inlist(tid, wls);
                    default: false;
                };
            default: true;
        }
    }
}

/*
 * If a mutex is owned by a task, then the owner is in the TCB mapping.
 */
predicate RH_TCBList_ECBList_MUTEX_OWNER(ECBMap ecbls, TCBMap tcbls) {
    forall (addrval eid in ecbls) {
        switch (get(eid, ecbls)) {
            case AbsECB{{edata: absmutexsem(P, some(owner{{tid: tid}})), wset: wls}}:
                indom(tid, tcbls);
            default: true;
        }
    }
}

/*
 * 1. For any mutex eid, if a task is in the waiting list of the mutex,
 *    then the corresponding TCB of the task is waiting for the same
 *    mutex.
 * 2. For any task tid, if the task is waiting for a mutex, then the
 *    task is in the waiting list of that mutex.
 */
predicate RH_TCBList_ECBList_MUTEX_P(ECBMap ecbls, TCBMap tcbls) {
    forall (addrval eid in ecbls) {
        switch (get(eid, ecbls)) {
            case AbsECB{{edata: absmutexsem(_, _), wset: wls}}:
                forall (addrval tid in wls) {
                    indom(tid, tcbls) &&
                    switch (get(tid, tcbls)) {
                        case AbsTCB{{stat: wait(os_stat_mutexsem(eid2), _)}}:
                            eid == eid2;
                        default: false;
                    }
                };
            default: true;
        }
    } &&
    forall (addrval tid in tcbls) {
        switch (get(tid, tcbls)) {
            case AbsTCB{{stat: wait(os_stat_mutexsem(eid), _)}}:
                indom(eid, ecbls) &&
                switch (get(eid, ecbls)) {
                    case AbsECB{{edata: absmutexsem(_, _), wset: wls}}:
                        inlist(tid, wls);
                    default: false;
                };
            default: true;
        }
    } &&
    RH_TCBList_ECBList_MUTEX_OWNER(ecbls, tcbls)
}

/*
 * Overall relationship between high-level TCB and ECB.
 */
predicate RH_TCBList_ECBList_P(ECBMap ecbls, TCBMap tcbls) {
    RH_TCBList_ECBList_Q_P(ecbls, tcbls) &&
    RH_TCBList_ECBList_SEM_P(ecbls, tcbls) &&
    RH_TCBList_ECBList_MBOX_P(ecbls, tcbls) &&
    RH_TCBList_ECBList_MUTEX_P(ecbls, tcbls)
}

// Mbox_common.v
// Setting the message of a mailbox
// Note this covers the case mbox_acpt_rh_tcblist_ecblist_p_hold
// (setting message to Vnull).
query mbox_rh_tcblist_ecblist_p_hold {
    fixes eid : addrval;
    fixes ecbls : ECBMap;
    fixes tcbls : TCBMap;
    fixes ecbls2 : ECBMap;
    fixes m : val;
    fixes m2 : val;
    fixes w : List<addrval>;
    assumes indom(eid, ecbls);
    assumes get(eid, ecbls) == AbsECB{{edata: absmbox(m), wset: w}};
    assumes RH_TCBList_ECBList_P(ecbls, tcbls);
    assumes mapUpdate(eid, AbsECB{{edata: absmbox(m2), wset: w}}, ecbls, ecbls2);
    shows RH_TCBList_ECBList_P(ecbls2, tcbls)
    proof { auto }
}

// sem_common.v
// Creating a semaphore

query semcre_RH_TCBList_ECBList_P {
    fixes eid : addrval;
    fixes ecbls : ECBMap;
    fixes tcbls : TCBMap;
    fixes ecbls2 : ECBMap;
    fixes i : int32u;
    assumes !indom(eid, ecbls);
    assumes RH_TCBList_ECBList_P(ecbls, tcbls);
    assumes mapUpdate(eid, AbsECB{{edata: abssem(i), wset: nil}}, ecbls, ecbls2);
    shows RH_TCBList_ECBList_P(ecbls2, tcbls)
    proof { auto(inlist_simps1<addrval>) }
}

// tasksuspend.v
/* TODO
query ECBList_P_preserve {
    fixes vptr : val;
    fixes ecbList : List<EventCtr>;
    fixes edls : List<leventdata>;
    fixes ecbls : ECBMap;
    fixes tcbls : TCBMap;
    fixes tcbls_new : TCBMap;
    fixes tid : addrval;
    fixes prio1 : int32u;
    fixes st1 : taskstatus;
    fixes msg1 : val;
    fixes sus1 : bool;
    assumes H1: ECBList_P(vptr, Vnull, ecbList, edls, ecbls, tcbls);
    assumes H2: get(tid, tcbls) == AbsTCB{{prio: prio1, stat: st1, msg: msg1, sus: sus1}};
    assumes H3: mapUpdate(tid, AbsTCB{{prio: prio1, stat: st1, msg: msg1, sus: true}}, tcbls, tcbls_new);
    shows ECBList_P(vptr, Vnull, ecbList, edls, ecbls, tcbls_new)
    proof {
        induction(ecbList){
            case nil: auto;
            case cons(ecb, ecbList2):
                cases(vptr) {
                    case Vptr(eid):
                        simplify;;
                        split_conj(H1, [H11, H12]);
                    default: auto;
                };
        }
    }
}
*/

query RL_TCBblk_P_suspend {
    fixes tcb : TCB;
    assumes RL_TCBblk_P(tcb);
    shows RL_TCBblk_P(tcb{stat := tcb.stat | OS_STAT_SUSPEND})
    proof { auto }
}

query R_TCB_Status_P_suspend {
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes rtbl2 : int32u[];
    fixes abstcb : AbsTCB;
    assumes prio_not_in_tbl(tcb.prio, rtbl2);
    assumes tcb.prio < 64;
    assumes R_TCB_Status_P(tcb, rtbl, abstcb);
    shows R_TCB_Status_P(tcb{stat := tcb.stat | OS_STAT_SUSPEND}, rtbl2, abstcb{sus := true})
    proof { auto }
}

query R_PrioTbl_P_suspend {
    fixes ptbl : val[];
    fixes tcbls : TCBMap;
    fixes tcbls_new : TCBMap;
    fixes vhold : addrval;
    fixes tid : addrval;
    fixes abstcb : AbsTCB;
    assumes R_PrioTbl_P(ptbl, tcbls, vhold);
    assumes indom(tid, tcbls) && get(tid, tcbls) == abstcb;
    assumes mapUpdate(tid, abstcb{sus := true}, tcbls, tcbls_new);
    shows R_PrioTbl_P(ptbl, tcbls_new, vhold)
    proof { auto }
}

query RH_TCBList_ECBList_P_suspend {
    fixes tid : addrval;
    fixes ecbls : ECBMap;
    fixes tcbls : TCBMap;
    fixes tcbls2 : TCBMap;
    fixes prio1 : int32u;
    fixes st1 : taskstatus;
    fixes msg1 : val;
    fixes sus1 : bool;
    assumes indom(tid, tcbls);
    assumes get(tid, tcbls) == AbsTCB{{prio: prio1, stat: st1, msg: msg1, sus: sus1}};
    assumes mapUpdate(tid, AbsTCB{{prio: prio1, stat: st1, msg: msg1, sus: true}}, tcbls, tcbls2);
    assumes RH_TCBList_ECBList_P(ecbls, tcbls);
    shows RH_TCBList_ECBList_P(ecbls, tcbls2)
    proof { auto }
}

// Mbox_common.v

query RH_TCBList_ECBList_P_high_block_hold_mbox {
    fixes ecbls : ECBMap;
    fixes tcbls : TCBMap;
    fixes qid : addrval;
    fixes pcur : addrval;
    fixes msgList : val;
    fixes wl: List<addrval>;
    fixes m1: val;
    fixes m2 : val;
    fixes sus1 : bool;
    fixes sus2 : bool;
    fixes prio : int32u;
    fixes ecbls2 : ECBMap;
    fixes tcbls2 : TCBMap;
    fixes time : int32u;
    assumes indom(qid, ecbls);
    assumes get(qid, ecbls) == AbsECB{{edata: absmbox(msgList), wset: wl}};
    assumes indom(pcur, tcbls);
    assumes get(pcur, tcbls) == AbsTCB{{prio: prio, stat: rdy, msg: m1, sus: sus1}};
    assumes RH_TCBList_ECBList_MBOX_P(ecbls, tcbls);
    assumes mapUpdate(qid, AbsECB{{edata: absmbox(msgList), wset: cons(pcur, wl)}}, ecbls, ecbls2);
    assumes mapUpdate(pcur, AbsTCB{{prio: prio, stat: wait(os_stat_mbox(qid), time), msg: m2, sus: sus2}}, tcbls, tcbls2);
    shows RH_TCBList_ECBList_MBOX_P(ecbls2, tcbls2)
    proof { auto }
}

query R_ECB_ETbl_P_high_tcb_block_hold {
    fixes tcbls : TCBMap;
    fixes tcbls_new : TCBMap;
    fixes eid : addrval;
    fixes ecb : EventCtr;
    fixes tid : addrval;
    fixes abstcb : AbsTCB;
    fixes y : int32u;
    fixes time : int32u;
    assumes Hprio : 0 < abstcb.prio && abstcb.prio < 64;
    assumes Hose : ecb.OSEventType == OS_EVENT_TYPE_MBOX;
    assumes H1 : R_ECB_ETbl_P(eid, ecb, tcbls);
    assumes H2 : indom(tid, tcbls) && get(tid, tcbls) == abstcb;
    assumes Hxy : y == abstcb.prio >> 3;
    assumes Hmapup : mapUpdate(tid, abstcb{stat := wait(os_stat_mbox(eid), time)}, tcbls, tcbls_new);
    shows R_ECB_ETbl_P(eid, ecb{OSEventGrp := ecb.OSEventGrp | (1 << y),
                                etbl := ecb.etbl[y := ecb.etbl[y] | (1 << (abstcb.prio & 7))]},
                       tcbls_new)
    proof { auto }
}

// The following theorems comes from OSTimeDlyPure.v

query R_PrioTbl_P_hold1 {
    fixes tid : addrval;
    fixes st : taskstatus;
    fixes tcbls : TCBMap;
    fixes ptbl : val[];
    fixes tcbls0 : TCBMap;
    fixes vhold : addrval;
    fixes abstcb : AbsTCB;
    assumes R_PrioTbl_P(ptbl, tcbls, vhold);
    assumes indom(tid, tcbls) && get(tid, tcbls) == abstcb;
    assumes mapUpdate(tid, abstcb{stat := st}, tcbls, tcbls0);
    shows R_PrioTbl_P(ptbl, tcbls0, vhold)
    proof { auto }
}

query RH_TCBList_ECBList_P_hold1 {
    fixes ecbls : ECBMap;
    fixes tcbls : TCBMap;
    fixes tcbls_new : TCBMap;
    fixes tid : addrval;
    fixes abstcb : AbsTCB;
    fixes i : int32u;
    assumes RH_TCBList_ECBList_P(ecbls, tcbls);
    assumes indom(tid, tcbls) && get(tid, tcbls) == abstcb;
    assumes switch (abstcb.stat) {
        case rdy: true;
        case wait(os_stat_time, _): true;
        default: false;
    };
    assumes mapUpdate(tid, abstcb{stat := wait(os_stat_time, i)}, tcbls, tcbls_new);
    shows RH_TCBList_ECBList_P(ecbls, tcbls_new)
    proof { auto }
}

query ecb_etbl_prop {
    fixes tid : addrval;
    fixes tcbls : TCBMap;
    fixes tcbls_new : TCBMap;
    fixes abstcb : AbsTCB;
    fixes eid : addrval;
    fixes ecb : EventCtr;
    fixes i : int32u;
    assumes indom(tid, tcbls) && get(tid, tcbls) == abstcb;
    assumes switch (abstcb.stat) {
        case rdy: true;
        case wait(os_stat_time, _): true;
        default: false;
    };
    assumes mapUpdate(tid, abstcb{stat := wait(os_stat_time, i)}, tcbls, tcbls_new);
    assumes R_ECB_ETbl_P(eid, ecb, tcbls);
    shows R_ECB_ETbl_P(eid, ecb, tcbls_new)
    proof { auto }
}

query low_stat_rdy_imp_high {
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes abstcb : AbsTCB;
    assumes RL_TCBblk_P(tcb);
    assumes R_TCB_Status_P(tcb, rtbl, abstcb);
    assumes tcb.stat == OS_STAT_RDY;
    assumes tcb.dly == 0;
    shows abstcb.stat == rdy
    proof { auto }
}

query low_stat_nordy_imp_high {
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes abstcb : AbsTCB;
    assumes R_TCB_Status_P(tcb, rtbl, abstcb);
    assumes (tcb.stat != OS_STAT_RDY || tcb.dly != 0);
    shows !(abstcb.stat == rdy && abstcb.sus == false)
    proof { auto }
}

query RLH_Rdy_prioneq_prop_hold {
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes abstcb : AbsTCB;
    fixes prio : int32u;
    assumes prio != tcb.prio;
    assumes RLH_RdyI_P(tcb, rtbl, abstcb);
    shows let grp = rtbl[prio >> 3] in
            RLH_RdyI_P(tcb, rtbl[prio >> 3 := grp & ~(1 << (prio & 7))], abstcb)
          end
    proof { auto }
}

query RHL_Rdy_prioneq_prop_hold {
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes abstcb : AbsTCB;
    fixes prio : int32u;
    assumes prio != tcb.prio;
    assumes prio < 64;
    assumes RHL_RdyI_P(tcb, rtbl, abstcb);
    shows let grp = rtbl[prio >> 3] in
            RHL_RdyI_P(tcb, rtbl[prio >> 3 := grp & ~(1 << (prio & 7))], abstcb)
          end
    proof { auto }
}

query RLH_Suspend_prioneq_prop_hold {
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes abstcb : AbsTCB;
    fixes prio : int32u;
    assumes prio != tcb.prio;
    assumes prio < 64;
    assumes RLH_Suspend_P(tcb, rtbl, abstcb);
    shows let grp = rtbl[prio >> 3] in
            RLH_Suspend_P(tcb, rtbl[prio >> 3 := grp & ~(1 << (prio & 7))], abstcb)
          end
    proof { auto }
}

query RHL_Suspend_prioneq_prop_hold {
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes abstcb : AbsTCB;
    fixes prio : int32u;
    assumes prio != tcb.prio;
    assumes prio < 64;
    assumes RHL_Suspend_P(tcb, rtbl, abstcb);
    shows let grp = rtbl[prio >> 3] in
            RHL_Suspend_P(tcb, rtbl[prio >> 3 := grp & ~(1 << (prio & 7))], abstcb)
          end
    proof { auto }
}

query RLH_Wait_prioneq_prop_hold {
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes abstcb : AbsTCB;
    fixes prio : int32u;
    assumes prio != tcb.prio;
    assumes prio < 64;
    assumes RLH_TCB_Status_Wait_P(tcb, rtbl, abstcb);
    shows let grp = rtbl[prio >> 3] in
            RLH_TCB_Status_Wait_P(tcb, rtbl[prio >> 3 := grp & ~(1 << (prio & 7))], abstcb)
          end
    proof { auto }
}

query RHL_Wait_prioneq_prop_hold {
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes abstcb : AbsTCB;
    fixes prio : int32u;
    assumes prio != tcb.prio;
    assumes prio < 64;
    assumes RHL_TCB_Status_Wait_P(tcb, rtbl, abstcb);
    shows let grp = rtbl[prio >> 3] in
            RHL_TCB_Status_Wait_P(tcb, rtbl[prio >> 3 := grp & ~(1 << (prio & 7))], abstcb)
          end
    proof { auto }
}

query rtbl_remove_RL_RTbl_PrioTbl_P_hold {
    fixes prio : int32u;
    fixes bitx : int32u;
    fixes rtbl : int32u[];
    fixes ptbl : val[];
    fixes vhold : addrval;
    assumes 0 <= prio && prio < 64;
    assumes RL_RTbl_PrioTbl_P(rtbl, ptbl, vhold);
    shows let grp = rtbl[prio >> 3] in
            RL_RTbl_PrioTbl_P(rtbl[prio >> 3 := grp & ~(1 << (prio & 7))], ptbl, vhold)
          end
    proof { auto }
}

// Combination of the above results. Only this is really needed.
query TCBNode_P_prioneq_prop_hold {
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes abstcb : AbsTCB;
    fixes prio : int32u;
    assumes prio != abstcb.prio;
    assumes prio < 64;
    assumes TCBNode_P(tcb, rtbl, abstcb);
    shows TCBNode_P(tcb, rtbl[prio >> 3 := rtbl[prio >> 3] & ~(1 << (prio & 7))], abstcb)
    proof { auto }
}

query map_get_test {
    fixes tid2 : addrval;
    fixes abstcb2 : AbsTCB;
    fixes tcbls : TCBMap;
    fixes prio : int32u;
    fixes tcbls_join : TCBMap;
    assumes join(tid2, abstcb2, tcbls, tcbls_join);
    assumes forall (addrval tid in tcbls_join) {
        get(tid, tcbls_join).prio != prio
    };
    shows forall (addrval tid in tcbls) {
        get(tid, tcbls).prio != prio
    }
    proof { auto }
}

query tcbjoin_join_get_neq {
    fixes ptcb : addrval;
    fixes a : AbsTCB;
    fixes tcbls1 : TCBMap;
    fixes tcbls2 : TCBMap;
    assumes join(ptcb, a, tcbls1, tcbls2);
    shows forall (addrval tid, AbsTCB b) {
        tid != ptcb -> indom(tid, tcbls1) -> get(tid, tcbls1) == get(tid, tcbls2)
    }
    proof { auto }
}

query TCBList_P_tcb_dly_hold1 {
    fixes time : int32u;
    fixes tcb : TCB;
    fixes rtbl : int32u[];
    fixes abstcb : AbsTCB;
    assumes H1 : 0 < time && time <= 65535;
    assumes H2 : TCBNode_P(tcb, rtbl, abstcb);
    assumes H3 :
        switch (abstcb.stat) {
            case rdy: abstcb.sus == false;
            case wait(os_stat_time, _): true;
            default: false;
        };
    shows TCBNode_P(
        tcb{dly := time},
        rtbl[tcb.y := rtbl[tcb.y] & ~tcb.bitx],
        abstcb{stat := wait(os_stat_time, time)}
    )
    proof { auto }
}

del_attrib rewrite for TCBNode_P_def

query update_rtbl_tcblist_hold {
    fixes vptr : val;
    fixes tcbList: TCBList;
    fixes rtbl : int32u[];
    fixes tcbls : TCBMap;
    fixes prio : int32u;
    assumes H1: forall (addrval tid in tcbls) {
        get(tid, tcbls).prio != prio
    };
    assumes H2: TCBList_P(vptr, tcbList, rtbl, tcbls);
    assumes H3: prio < 64;
    shows TCBList_P(vptr, tcbList, rtbl[prio >> 3 := rtbl[prio >> 3] & ~(1 << (prio & 7))], tcbls)
    proof {
        induction(tcbList, [vptr, tcbls]) {
            case nil: auto;
            case cons(tcb, rest):
                cases(vptr) {
                    case Vptr(tid):
                        simplify;;
                        skolemize(H2, [AbsTCB abstcb2, TCBMap tcbls2]);;
                        split_conj(H2, [H21, H22, H23]);;
                        match_show(H23) {
                            1: apply_theorem(TCBNode_P_prioneq_prop_hold, [_, H3, H21]);;
                               auto;
                            2: apply_theorem(IH_rest, [_, H22]);;
                               apply_theorem(map_get_test, [H23, H1]);
                        };
                    default: auto;
                };
        }
    }
}

query TCBList_P_tcb_dly_hold {
    fixes tcbList : TCBList;
    fixes rtbl : int32u[];
    fixes vptr : val;
    fixes tcbls : TCBMap;
    fixes prio : int32u;
    fixes ptcb : addrval;
    assumes H1 : prio < 64;
    assumes H2 : TCBList_P(vptr, tcbList, rtbl, tcbls);
    assumes H3 : !indom(ptcb, tcbls);
    assumes H4 : prio_neq_cur(tcbls, ptcb, prio);
    shows TCBList_P(vptr, tcbList, rtbl[prio >> 3 := rtbl[prio >> 3] & ~ (1 << (prio & 7))], tcbls)
    proof {
        apply_theorem(update_rtbl_tcblist_hold, [_, H2, H1]);;
        auto
    }
}

query TCBList_P_tcb_dly_hold2 {
    fixes time : int32u;
    fixes tcb : TCB;
    fixes tcbList : TCBList;
    fixes rtbl : int32u[];
    fixes ptcb : addrval;
    fixes abstcb : AbsTCB;
    fixes tcbls : TCBMap;
    fixes tcbls2 : TCBMap;
    assumes H0 : RL_TCBblk_P(tcb);
    assumes H1 : 0 < time && time <= 65535;
    assumes H2 : TCBList_P(Vptr(ptcb), cons(tcb, tcbList), rtbl, tcbls);
    assumes H3 : indom(ptcb, tcbls) && get(ptcb, tcbls) == abstcb;
    assumes H4 :
        switch (abstcb.stat) {
            case rdy: abstcb.sus == false;
            case wait(os_stat_time, _): true;
            default: false;
        };
    assumes H5 : prio_neq_cur(tcbls, ptcb, tcb.prio);
    assumes H6 : mapUpdate(ptcb, abstcb{stat := wait(os_stat_time, time)}, tcbls, tcbls2);
    shows TCBList_P(Vptr(ptcb), cons(tcb{dly := time}, tcbList), rtbl[tcb.y := rtbl[tcb.y] & ~tcb.bitx], tcbls2)
    proof { 
        simplify;;
        skolemize(H2, [AbsTCB abstcb2, TCBMap tcbls3]);;
        split_conj(H2, [H21, H22, H23]);;
        exists(abstcb{stat := wait(os_stat_time, time)}, tcbls3) {
            1: apply_theorem(TCBList_P_tcb_dly_hold1, [H1]) {
                1: auto;
                2: auto;
            };
            2: change (tcb.y == tcb.prio >> 3) { auto };;
               change (tcb.bitx == (1 << (tcb.prio & 7))) { auto };;
               assert (H5a: prio_neq_cur(tcbls3, ptcb, tcb.prio)) { auto };;
               apply_theorem(TCBList_P_tcb_dly_hold, [_, H22, _, H5a]) {
                 1: auto;
                 2: auto;
               };
            3: auto;
        }
    }
}

// task_pure.v

query r_priotbl_p_hold_for_del_a_tcb {
    fixes ptbl : val[];
    fixes abstcb : AbsTCB;
    fixes vhold : addrval;
    fixes head : addrval;
    fixes tcbls : TCBMap;
    fixes tcbls_left : TCBMap;
    assumes H1 : 0 <= abstcb.prio && abstcb.prio < 64;
    assumes H2 : R_PrioTbl_P(ptbl, tcbls, vhold);
    assumes H3 : join(head, abstcb, tcbls_left, tcbls);
    shows R_PrioTbl_P(ptbl[abstcb.prio := Vnull], tcbls_left, vhold)
    proof { auto }
}

query priowaitinq_is_prio_in_tbl {
    fixes prio : int32u;
    fixes rtbl : int32u[];
    assumes 0 <= prio && prio < 64;
    assumes prio_in_tbl(prio, rtbl);
    assumes exists(int32u z) { rtbl[prio >> 3] == z };
    shows PrioWaitInQ(prio, rtbl)
    proof { auto }
}

/*
 * Lemma used in task_pure.v.
 */
query ecb_no_exists_tcb_sub {
    fixes ecbls1 : ECBMap;
    fixes ecbls2 : ECBMap;
    fixes tcbls : TCBMap;
    assumes subseteq(ecbls1, ecbls2);
    assumes ecb_no_exists_tcb(ecbls2, tcbls);
    shows ecb_no_exists_tcb(ecbls1, tcbls)
    proof { auto }
}

query R_Prio_No_Dup_hold_for_subset {
    fixes tid : addrval;
    fixes abstcb : AbsTCB;
    fixes tcbls1 : TCBMap;
    fixes tcbls2 : TCBMap;
    assumes join(tid, abstcb, tcbls1, tcbls2);
    shows R_Prio_No_Dup(tcbls2) -> R_Prio_No_Dup(tcbls1)
    proof { auto }
}

query TcbIsWait {
    fixes tcb : TCB;
    fixes abstcb : AbsTCB;
    fixes rtbl : int32u[];
    assumes R_TCB_Status_P(tcb, rtbl, abstcb);
    assumes tcb.stat == OS_STAT_SEM || tcb.stat == OS_STAT_Q ||
            tcb.stat == OS_STAT_MBOX || tcb.stat == OS_STAT_MUTEX || 
            tcb.stat == (OS_STAT_SEM | OS_STAT_SUSPEND) || tcb.stat == (OS_STAT_Q | OS_STAT_SUSPEND) || 
            tcb.stat == (OS_STAT_MBOX | OS_STAT_SUSPEND) || tcb.stat == (OS_STAT_MUTEX | OS_STAT_SUSPEND);
    shows
        switch (tcb.eptr) {
            case Vptr(eid): true;
            default: false;
        } &&
        switch (abstcb.stat) {
            case wait(os_stat_sem(_), dly):
                dly == tcb.dly;
            case wait(os_stat_q(_), dly):
                dly == tcb.dly;
            case wait(os_stat_mbox(_), dly):
                dly == tcb.dly;
            case wait(os_stat_mutexsem(_), dly):
                dly == tcb.dly;
            default: false;
        }
    proof { auto }
}

query remove_tid_not_nil {
    fixes tid : addrval;
    fixes tidls : List<addrval>;
    assumes list_remove(tid, tidls) != nil;
    shows tidls != nil
    proof { auto }
}
