
(* ##################################################################################################### *)
(* ### In this file we describe a primitive multi-process synchronisation using file locks           ### *)
(* ### The lock mechanism relies on the fact that `mkdir` locks until the directory no longer exists ### *)
(* ##################################################################################################### *)

CCCLockDir = "/home/popolit/.locks/";
CCCFileLocksRetryTimeout = 10; (* ### << A timeout in seconds between successful locking tries ### *)
CCCEExistConst = 1;
EnsureLockDir[] :=
    (* ### ^^ Make sure the directory that contains locks does exist ### *)
    Module[{},
           Run[StringTemplate["mkdir -p `lockDir`"][<|"lockDir" -> CCCLockDir|>]]];
TryTakeALock[name_] :=
    (* ### ^^ Tries to take a lock with name `name`. Immediately returns, but returns ### *)
    (* ###    $Success, $StillLocked or $Failed depending on whether taking was successful.              ### *)
    Module[{},
           EnsureLockDir[];
           Module[{code = Run[StringTemplate["mkdir `lockDir``fname`"][<|"lockDir" -> CCCLockDir,
                                                                       "fname" -> name|>]]},
                  If[0 === code,
                     CreatePIDFile[name]; $Success,
                     If[1 === Mod[code, 255],
                        $StillLocked,
                        Message[TryTakeALock::unknownFailure, code]; $Failed]]]];
CreatePIDFile[name_] :=
    (* ### ^^ create a file with process id inside the lock-directory ### *)
    Run[StringTemplate["touch `lockDir``fname`/`pid`.pid"][<|"lockDir" -> CCCLockDir,
                                                           "fname" -> name,
                                                           "pid" -> $ProcessID|>]];
DeletePIDFile[name_] :=
    (* ### ^^ delete the process id file inside the lock-directory ### *)
    Run[StringTemplate["rm `lockDir``fname`/`pid`.pid"][<|"lockDir" -> CCCLockDir,
                                                        "fname" -> name,
                                                        "pid" -> $ProcessID|>]];
ReleaseALock[name_] :=
    (* ### ^^ Releases a lock. If there is already no lock, outputs $Failed (and a message), otherwise $Success. ### *)
    Module[{code = DeletePIDFile[name]},
           Module[{code = Run[StringTemplate["rmdir `lockDir``fname`"][<|"lockDir" -> CCCLockDir,
                                                                       "fname" -> name|>]]},
                  If[0 === code,
                     $Success,
                     If[1 === Mod[code, 255],
                        Message[ReleaseALock::codeOneFailure]; $Failed,
                        Message[ReleaseALock::unknownFailure, code]; $Failed]]]];
ForceReleaseALock[name_] :=
    (* ### ^^ Releases a lock, removing all the contents of the lock-dir. I.e. it ignores the PID of the process that created ### *)
    (* ###    a lock!!!. ### *)
    Module[{code = Run[StringTemplate["rm -r `lockDir``fname`"][<|"lockDir" -> CCCLockDir,
                                                                   "fname" -> name|>]]},
           If[0 === code,
              $Success,
              If[1 === Mod[code, 255],
                 Message[ReleaseALock::codeOneFailure]; $Failed,
                 Message[ReleaseALock::unknownFailure, code]; $Failed]]];
TakeALock[name_] :=
    (* ### ^^ Take a lock with a given name. Blocks until the lock is taken ### *)
    Module[{res = TryTakeALock[name]},
           While[$Success =!= res,
                 If[$StillLocked === res,
                    (* ### vv then ### *)
                    Print[StringTemplate["Lock still taken, retrying after `num` seconds"][<|"num" -> CCCFileLocksRetryTimeout|>]];
                    Pause[CCCFileLocksRetryTimeout];
                    res = TryTakeALock[name],
                    (* ### vv else ### *)
                    Return[$Failed]]];
           res];
WithALock[name_, body_] :=
    (* ### ^^ Evaluate body with lock `name` taken. As mathematica does not properly have stack unwinding ### *)
    (* ###    on exceptions, this may deadlock if something goes wrong ### *)
    Module[{res = TakeALock[name]},
           If[$Failed =!= res,
              Module[{expr = CompoundExpression[body]},
                     ReleaseALock[name];
                     expr],
              $Failed]];


