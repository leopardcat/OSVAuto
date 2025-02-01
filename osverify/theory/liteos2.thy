imports basic

// Use int32u to represent task ID
typedef TaskID = int32u;

enum AbsStatus =
    unused
  | ready
  | running(int64u time)
  | exit
  | pend
  | pendtime(int64u time)
  | delay(int64u time)

struct AbsTaskState {
    AbsStatus status;
    int32u tPrio;
    bool suspend;
}

struct AbsGlobalState {
    Map<TaskID, AbsTaskState> usedTask;
    Seq< Seq<TaskID> > g_priQueueList;
    int32u g_queueBitmap [binary];
}

predicate is_ready(AbsTaskState state) {
    !state.suspend &&
    switch (state.status) {
        case ready: true;
        default: false;
    }
}

/*
 * For each priority, the corresponding linked list is empty iff the
 * corresponding bit in the queueBitmap is off.
 */
predicate priority_bitmap_inv(AbsGlobalState gstate) {
    seq_length(gstate.g_priQueueList) == 32 &&
    forall (int32u prio in range(0, 32)) {
        if (seq_length(gstate.g_priQueueList[int(prio)]) == 0) {
            gstate.g_queueBitmap & (1 << prio) == 0
        } else {
            gstate.g_queueBitmap & (1 << prio) == 1 << prio
        }
    }
}

predicate pri_queue_list_unique(AbsGlobalState gstate) {
    forall (int32u prio in range(0, 32)) {
        forall (int i, int j) {
            0 <= i && i < seq_length(gstate.g_priQueueList[int(prio)]) &&
            0 <= j && j < seq_length(gstate.g_priQueueList[int(prio)]) && i != j ->
            seq_index(i, gstate.g_priQueueList[int(prio)]) !=
            seq_index(j, gstate.g_priQueueList[int(prio)])
        }
    }
}

/*
 * Each task in the priority queue list must be part of usedTask,
 * and the priority and status must be the consistent.
 */
predicate pri_queue_list_used_task_rel(AbsGlobalState gstate) {
    forall (int32u prio in range(0, 32)) {
        forall (int i) {
            i >= 0 && i < seq_length(gstate.g_priQueueList[int(prio)]) ->
            let task_id = gstate.g_priQueueList[int(prio)][i] in
                indom(task_id, gstate.usedTask) &&
                let tsk = get(task_id, gstate.usedTask) in
                    tsk.tPrio == prio &&
                    is_ready(tsk)
                end
            end
        }
    }
}

/*
 * For each task in usedTask, if the task is ready, then it must appear
 * in the corresponding g_priQueueList.
 */
predicate pri_queue_list_used_task_rel2(AbsGlobalState gstate) {
    forall (TaskID task_id in gstate.usedTask) {
        let tsk = get(task_id, gstate.usedTask) in
            is_ready(tsk) ->
            exists (int j) {
                j >= 0 && j < seq_length(gstate.g_priQueueList[int(tsk.tPrio)]) &&
                gstate.g_priQueueList[int(tsk.tPrio)][j] == task_id
            }
        end
    }
}

/*
 * Priority of each task is in range.
 */
predicate used_task_prio_in_range(AbsGlobalState gstate) {
    forall (TaskID task_id in gstate.usedTask) {
        let tsk = get(task_id, gstate.usedTask) in
            0 <= tsk.tPrio && tsk.tPrio < 32
        end
    }
}

/*
 * Collection of global state invariants.
 */
predicate gstate_inv(AbsGlobalState gstate) {
    priority_bitmap_inv(gstate) &&
    used_task_prio_in_range(gstate) &&
    pri_queue_list_unique(gstate) &&
    pri_queue_list_used_task_rel(gstate) &&
    pri_queue_list_used_task_rel2(gstate)
}

/*
 * Valid transition from gstate to gstate2,
 */
predicate task_suspend_rel(AbsGlobalState gstate, AbsGlobalState gstate2, TaskID task_id) {
    indom(task_id, gstate.usedTask) &&
    let tsk = get(task_id, gstate.usedTask) in
        is_ready(tsk) &&
        gstate2.usedTask == updateMap(task_id, tsk{suspend := true}, gstate.usedTask) &&
        exists (int j) {
            j >= 0 && j < seq_length(gstate.g_priQueueList[int(tsk.tPrio)]) &&
            gstate.g_priQueueList[int(tsk.tPrio)][j] == task_id &&
            gstate2.g_priQueueList[int(tsk.tPrio)] == seq_remove(j, gstate.g_priQueueList[int(tsk.tPrio)]) &&
            if (seq_length(seq_remove(j, gstate.g_priQueueList[int(tsk.tPrio)])) == 0) {
                gstate2.g_queueBitmap == gstate.g_queueBitmap & (~(1 << tsk.tPrio))
            } else {
                gstate2.g_queueBitmap == gstate.g_queueBitmap
            }
        } &&
        seq_length(gstate2.g_priQueueList) == seq_length(gstate.g_priQueueList) &&
        forall (int32u prio in range(0, 32)) {
            prio != tsk.tPrio -> gstate.g_priQueueList[int(prio)] == gstate2.g_priQueueList[int(prio)]
        }
    end
}

query task_suspend_correct1 {
    fixes gstate : AbsGlobalState;
    fixes gstate2 : AbsGlobalState;
    fixes task_id : TaskID;
    assumes H1: gstate_inv(gstate);
    assumes H2: task_suspend_rel(gstate, gstate2, task_id);
    shows priority_bitmap_inv(gstate2)
    proof {
        seq_auto
    }
}

query task_suspend_correct2 {
    fixes gstate : AbsGlobalState;
    fixes gstate2 : AbsGlobalState;
    fixes task_id : TaskID;
    assumes H1: gstate_inv(gstate);
    assumes H2: task_suspend_rel(gstate, gstate2, task_id);
    shows used_task_prio_in_range(gstate2)
    proof {
        seq_auto
    }
}

query task_suspend_correct3 {
    fixes gstate : AbsGlobalState;
    fixes gstate2 : AbsGlobalState;
    fixes task_id : TaskID;
    assumes H1: gstate_inv(gstate);
    assumes H2: task_suspend_rel(gstate, gstate2, task_id);
    shows pri_queue_list_unique(gstate2)
    proof {
        seq_auto
    }
}

query task_suspend_correct4 {
    fixes gstate : AbsGlobalState;
    fixes gstate2 : AbsGlobalState;
    fixes task_id : TaskID;
    assumes H11: priority_bitmap_inv(gstate);
    assumes H12: used_task_prio_in_range(gstate);
    assumes H13: pri_queue_list_unique(gstate);
    assumes H14: pri_queue_list_used_task_rel(gstate);
    assumes H2: task_suspend_rel(gstate, gstate2, task_id);
    shows pri_queue_list_used_task_rel(gstate2)
    proof {
        seq_auto
    }
}

query task_suspend_correct5 {
    fixes gstate : AbsGlobalState;
    fixes gstate2 : AbsGlobalState;
    fixes task_id : TaskID;
    assumes H1: gstate_inv(gstate);
    assumes H2: task_suspend_rel(gstate, gstate2, task_id);
    shows pri_queue_list_used_task_rel2(gstate2)
    proof {
        seq_auto
    }
}
