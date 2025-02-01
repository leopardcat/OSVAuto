imports seq

typedef TaskID = int32u;

const int16u OS_TASK_STATUS_UNUSED = 1;
const int16u OS_TASK_STATUS_SUSPEND = 2;
const int16u OS_TASK_STATUS_READY = 4;
const int16u OS_TASK_STATUS_PEND = 8;
const int16u OS_TASK_STATUS_RUNNING = 16;
const int16u OS_TASK_STATUS_DELAY = 32;
const int16u OS_TASK_STATUS_TIMEOUT = 64;
const int16u OS_TASK_STATUS_PEND_TIME = 128;
const int16u OS_TASK_STATUS_EXIT = 256;

struct TCB {
    int16u taskStatus;
    int32u priority;
}

struct Global {
    // Array of task control blocks, fixed length MAX_TASK
    Seq<TCB> g_taskCBArray;

    // List of ready tasks for each priority, fixed length 32
    Seq< Seq<TaskID> > g_priQueueList;

    // Bitmap of priorities
    int32u g_queueBitmap;
}

/*
 * For each priority, the corresponding list of ready tasks is empty
 * iff the corresponding bit in the queueBitmap is off.
 */
predicate priority_bitmap_inv(Global global) {
    forall (int32u prio in range(0, 32)) {
        if (seq_length(global.g_priQueueList[int(prio)]) == 0) {
            global.g_queueBitmap & (1 << prio) == 0
        } else {
            global.g_queueBitmap & (1 << prio) == 1 << prio
        }
    }
}

function OsSchedPriQueueEnHead(Global global, TaskID taskID, int32u priority) -> Global {
    let global2 =
        if (seq_length(global.g_priQueueList[int(priority)]) == 0) {
            global{g_queueBitmap := global.g_queueBitmap | (1 << priority)}
        } else {
            global
        } in
        global2{|g_priQueueList[int(priority)] :=
                    seq_append(seq_repeat(taskID, 1),
                               global.g_priQueueList[int(priority)])|}
    end
}

function OsSchedPriQueueEnTail(Global global, TaskID taskID, int32u priority) -> Global {
    let global2 =
        if (seq_length(global.g_priQueueList[int(priority)]) == 0) {
            global{g_queueBitmap := global.g_queueBitmap | (1 << priority)}
        } else {
            global
        } in
        global2{|g_priQueueList[int(priority)] :=
                    seq_append(global.g_priQueueList[int(priority)],
                               seq_repeat(taskID, 1))|}
    end
}

function OsSchedPriQueueDelete(Global global, int index, int32u priority) -> Global {
    let global2 =
        global{|g_priQueueList[int(priority)] :=
                    seq_remove(index, global.g_priQueueList[int(priority)])|} in
        if (seq_length(global2.g_priQueueList[int(priority)]) == 0) {
            global2{g_queueBitmap := global.g_queueBitmap & (~(1 << priority))}
        } else {
            global2
        }
    end
}

query OsSchedPriQueueEnHead_inv {
    fixes global : Global;
    fixes taskID : TaskID;
    fixes priority : int32u;
    assumes priority_bitmap_inv(global);
    shows priority_bitmap_inv(OsSchedPriQueueEnHead(global, taskID, priority))
    proof { seq_auto }
}

query OsSchedPriQueueEnTail_inv {
    fixes global : Global;
    fixes taskID : TaskID;
    fixes priority : int32u;
    assumes priority_bitmap_inv(global);
    shows priority_bitmap_inv(OsSchedPriQueueEnTail(global, taskID, priority))
    proof { seq_auto }
}

query OsSchedPriQueueDelete_inv {
    fixes global : Global;
    fixes index : int;
    fixes priority : int32u;
    assumes priority_bitmap_inv(global);
    shows priority_bitmap_inv(OsSchedPriQueueDelete(global, index, priority))
    proof { seq_auto }
}
