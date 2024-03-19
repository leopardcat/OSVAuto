struct addrval {
    int32u block;
    int32u offset;
}

datatype val =
    Vundef | Vnull | Vint32(int32u n) | Vptr(addrval addr)

struct TCB {
    val next;
    val prev;
    val eptr;
    val msg;
    int32u dly;
    int32u stat;
    int32u prio;
    int32u x;
    int32u y;
    int32u bitx;
    int32u bity;
    int32u flag;
}

struct OSEvent {
    int32u OSEventType;
    int32u OSEventGrp;
    int32u OSEventCnt;
    val OSEventPtr;
    val OSEventListPtr;
}

consts {
    OS_STAT_RDY = 0;
    OS_STAT_SEM = 1;
    OS_STAT_MBOX = 2;
    OS_STAT_Q = 4;
    OS_STAT_SUSPEND = 8;
    OS_STAT_MUTEX = 16;
    OS_STAT_FLAG = 32;
    OS_LOWEST_PRIO = 63;
    OS_EVENT_TYPE_UNUSED = 0;
    OS_EVENT_TYPE_MBOX = 1;
    OS_EVENT_TYPE_Q = 2;
    OS_EVENT_TYPE_SEM = 3;
    OS_EVENT_TYPE_MUTEX = 4;
}

datatype tcbstats = 
    os_stat_sem (addrval ev)
  | os_stat_q (addrval ev)
  | os_stat_time
  | os_stat_mbox (addrval ev)
  | os_stat_mutexsem (addrval ev)

datatype taskstatus =
    rdy | wait(tcbstats stat, int32u time)

struct AbsTCB {
    int32u prio;
    taskstatus stat;
    val msg;
    bool sus;
}

typedef TCBMap = Map<addrval, struct AbsTCB>;

typedef TCBList = List<struct TCB>;

typedef PTBLMap = Map<int32u, val>;

/**********************
* Definition of event *
**********************/

/*
 * Owner of mutex.
 * tid - pointer to the owning task.
 * oprio - original priority of the owning task. The owning task is
 *         temporarily set to a higher priority.
 */
struct owner {
    addrval tid;
    int32u oprio;
}    

/*
 * Abstract event data
 *
 * For semaphore, specifies semaphore count.
 * For message queue, specifies list of messages, maximum size of the queue,
 *     and list of tasks waiting to push.
 * For mailbox, address to the message.
 * For mutex, priority of the mutex, and optionally information for its owner.
 */
datatype eventdata =
    abssem(int32u count)
  | absmsgq(List<val> msgl, int32u qsize)
  | absmbox(val msg)
  | absmutexsem(int32u prio, Option<owner> owner)

/*
 * Abstract event control block
 *
 * Specifies event information, and list of tasks waiting for the event.
 */
struct AbsECB {
    eventdata edata;
    List<addrval> wset;
}

// Mapping from address to abstract ECB
typedef ECBMap = Map<addrval, struct AbsECB>;

// Structure of low-level queue
struct osqueue {
    addrval qptr;
    addrval qstart;
    addrval qend;
    addrval qin;
    addrval qout;
    int32u qsize;
    int32u qentries;
}

/*
 * Data structure for low-level event data
 *
 * For message queue, the fields are:
 *   a -
 *   osq - low-level message queue information
 *   osqblk -
 *   msgtbl - low-level list of messages
 *
 * For semaphore, the fields are:
 *   count - semaphore count
 *
 * For mailbox, the fields are:
 *   msg - pointer to the message
 *
 * For mutex, the fields are:
 *   x - 16-bit integer, where the higher 8 bit contains priority of the
 *       mutex. If the lower 8 bit is 255, then the mutex is not owned,
 *       otherwise it is the original priority of the owner.
 *   y - mutex owner, either Vnull (not owned) or Vptr(tid), where tid is
 *       the owning task
 */
datatype leventdata =
    DMsgQ(val a, osqueue osq, List<val> osqblk, List<val> msgtbl)
  | DSem(int32u count)
  | DMbox(val msg)
  | DMutex(val x, val y)

// Definition of EventCtr
struct EventCtr {
    struct OSEvent osevent;
    int32u[] etbl;
}