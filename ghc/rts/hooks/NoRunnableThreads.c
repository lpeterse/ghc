/* -----------------------------------------------------------------------------
 * $Id: NoRunnableThreads.c,v 1.4 2002/07/18 06:05:31 sof Exp $
 *
 * User-overridable RTS hooks.
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"

#include <stdio.h>
#include <stdlib.h>

/*
  Hook to invoke when there's nothing left on the runnable threads
  queue {\em and} we've got nothing to wait for. The value
  returned is the exit code to report back. 
  
  NOTE: This hook is really CONCURRENT specific, but we include
  it in the way-independent libHSclib.a.
*/

int
NoRunnableThreadsHook (void)
{
    fflush(stdout);
    fprintf(stderr, "No runnable threads!\n");
    return(EXIT_FAILURE);
}

