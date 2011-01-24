#ifndef _system_supervisorinterface_h_
#define _system_supervisorinterface_h_

    #ifndef _REENTRANT
      #define _REENTRANT
    #endif
    #include <pthread.h>
    #define GC_THREADS
    #include <gc/gc.h>

typedef void* (*ThreadTaskFunctionPtr)(void*);

#define GETSPECIFICTHREADLOCAL
#ifdef GETSPECIFICTHREADLOCAL
#define THREADLOCAL(x,typ) (*((typ*)TS_Get_Local(x##_id)))
#define THREADLOCALDECL(typ,x) int x##_id
#define THREADLOCALINIT(x) TS_Add_ThreadLocal(&x##_id,#x)
#else
#define THREADLOCAL(x,typ) x
#define THREADLOCALDECL(typ,x) typ x
#define THREADLOCALINIT(x) x
#endif


#ifdef __cplusplus
extern "C" {
#endif

  //Public interface functions
  struct ThreadSupervisor;
  struct ThreadTask;
  extern void* waitOnTask(struct ThreadTask* task);
  extern void addCancelTask(struct ThreadTask* task, struct ThreadTask* cancel);
  extern void pushTask(struct ThreadTask* task);
  extern void addStartTask(struct ThreadTask* task, struct ThreadTask* start);
  extern void addDependency(struct ThreadTask* task, struct ThreadTask* start);
  /** 
      Returns 1 if the task is finished, 0 otherwise
  **/
  extern int taskDone(struct ThreadTask* task);
  /**
     Returns 1 if the task has been started, 0 otherwise
  **/
  extern int taskStarted(struct ThreadTask* task);
  /**
     Returns the taskResult if finished, NULL otherwise
  **/
  extern void* taskResult(struct ThreadTask* task);
  /**
     Returns 1 if the task should keep running, 0 otherwise
  **/
  extern int taskKeepRunning(struct ThreadTask* task);
  /**
     Interrupt the task
   **/
  extern void taskInterrupt(struct ThreadTask* task);

  extern struct ThreadTask* createThreadTask(const char* name, ThreadTaskFunctionPtr func, void* userData, int timeLimitExists, time_t timeLimitSeconds, int isM2Task);

  //Private interface functions
  extern THREADLOCALDECL(struct atomic_field, interrupts_interruptedFlag);
  extern THREADLOCALDECL(struct atomic_field, interrupts_exceptionFlag);
  extern struct ThreadSupervisor* threadSupervisor;
  struct parse_ThreadCellBody_struct;
  void createThreadGCMemory();
  extern void delThread(pthread_t thread);
  extern void initializeThreadSupervisor();
  static inline struct ThreadTask* runM2Task(ThreadTaskFunctionPtr fptr, void* userData) {
    struct ThreadTask* task = createThreadTask("M2Task",fptr,userData,0,0,1);
    pushTask(task);
    return task;
  }
  /**
     Create an M2 task without queueing it
  **/
  static inline struct ThreadTask* createM2Task(ThreadTaskFunctionPtr fptr, void* userData) {
    struct ThreadTask* task = createThreadTask("M2Task",fptr,userData,0,0,1);
    return task;
  }
#ifdef GETSPECIFICTHREADLOCAL
  extern void TS_Add_ThreadLocal(int* refno, const char* name);
  static void** TS_Get_LocalArray() {  return (void**)pthread_getspecific(*(pthread_key_t*)threadSupervisor); }
  static void** TS_Get_Local(int refno) { return &TS_Get_LocalArray()[refno]; }
#endif
  
     
#ifdef __cplusplus
}
#endif



#endif