

          /* *************************************************** */
	  /*                                                     */
	  /*       XHOLHELP: THE HOL DOCUMENTATION BROWSER       */
	  /*                                                     */
	  /*                           - Sara Kalvala            */
	  /*                           University of Cambridge   */
	  /*                           Computer Laboratory       */
	  /*                           (sk@cl.cam.ac.uk)         */
	  /*                           August, 1991              */
	  /*                                                     */
          /* *************************************************** */
	  /* HISTORY                                             */
	  /*                                                     */
	  /* Added some dialog boxes for editing help & theorems */
	  /* paths. Justification: The environment variables are */
	  /* fixed at the start of the session; now the path can */
	  /* be updated dynamically without qutting xholhelp.    */
	  /*                                                     */
	  /* Changed functionality in doA so that apropos on an  */
	  /* empty dialog value just returns a list of all known */
	  /* help files. This is much faster than getting the 2  */
	  /* line synopsis from all known help files (which can  */
	  /* still be achieved by invoking apropos on blank but  */
	  /* non empty dialog (Bug or Feature?!)                 */
	  /*                                                     */
	  /*                 Matthew J Morley (mjm@lfcs.ed.ac.uk)*/
	  /*                  Feb, 1993                          */
	  /*                                                     */
          /* *************************************************** */

#include <stdio.h>

#include <X11/Xatom.h>
#include <X11/Intrinsic.h>
#include <X11/StringDefs.h>
#include <X11/Shell.h>

#include <X11/Xaw/AsciiText.h>
#include <X11/Xaw/Box.h>
#include <X11/Xaw/Command.h>
#include <X11/Xaw/Dialog.h>
#include <X11/Xaw/Paned.h>
#include <X11/Xaw/Label.h>
#include <X11/Xaw/List.h>
#include <X11/Xaw/Toggle.h>
#include <X11/Xaw/Form.h>

#include <X11/Xmu/Atoms.h>
#include <X11/Xmu/StdSel.h>

#include <X11/Xaw/Cardinals.h>
#include <X11/cursorfont.h>

#include "xholhelp.h"

void Quit(), doA(), doR(), doT(), Help(), ClearD(), ScrollF(), ScrollB(), 
     ShowData(), busyCursor(), unbusyCursor(), PrintOut(),
     Go(), Update(), Popup(), Cancel();

static char help_path[MAXLEN], thms_path[MAXLEN];

static String fallback_resources[] = { 
  "xholhelp.height: 400",
  "xholhelp.width: 600",
  "*showGrip: False",
  "*font: 7x13bold",
  "*allowShellResize: TRUE",

/* dialog box */

  "*dialog.label.height: 2",
  "*dialog.label: ",
  "*dialog.value: ",

  "*dialog.value.translations:  #override \\n \
                 <Key>Escape: doR() \\n \
                 <Key>Return: doA() \\n \
                 <Key>Tab:    doT() \\n \
             Ctrl<Key>L: ClearD() \\n \
             Ctrl<Key>V: ScrollF() \\n \
             Ctrl<Key>N: ScrollF() \\n \
             Meta<Key>V: ScrollB() \\n \
             Ctrl<Key>P: ScrollB() \\n \
             Ctrl<Key>Q: Quit()",

/* POPUP WINDOWS SEMANTICS: See below, where the buttons are created */

  "*edithelp.label.height: 12",
  "*edithelp.label: Edit the help path:",
  "*edithelp.value.translations: #override \\n \
                   <Key>Return: Go()",            /* commit changes to path  */

  "*editthms.label.height: 12",
  "*editthms.label: Edit the theorem help path:",
  "*editthms.value.translations: #override \\n \
                   <Key>Return: Go()",            /* commit changes to path  */

  "*dialog*theorems.translations: #override \\n \
                 <Btn1Down>:  doT() \\n \
                 <Btn3Down>:  Popup()",           /* popup action under RM   */

/* command buttons */

  "*Command.height: 20",

/* box for text - default is help */

  "*text*type: file",
  "*text*string: HELPFILE",
  "*text*scrollVertical: always",
  "*text*displayCaret: False",
  "*text*translations: #override  \\n \
         <Key>Escape: doR() \\n \
         <Key>Return: doA() \\n \
         <Key>Tab:    doT() \\n \
     Ctrl<Key>V: ScrollF() \\n \
     Ctrl<Key>N: ScrollF() \\n \
     Meta<Key>V: ScrollB() \\n \
     Ctrl<Key>P: ScrollB() \\n \
     Ctrl<Key>L: ClearD() \\n \
     Ctrl<Key>Q: Quit()",
NULL, };

XtActionsRec actionTable[] = {
    {"doA",     doA},
    {"doR",     doR},
    {"doT",     doT},
    {"ScrollF", ScrollF},
    {"ScrollB", ScrollB},
    {"ClearD",  ClearD},
    {"Quit",    Quit},
    {"Go",      Go},
    {"Popup",   Popup}
};

  Widget holapropos, outer, dialog, quit, help, apropos, printout,
         entry, theorems, clear, scrollf, scrollb, alltext, 
         pathedit, help_popup, edithelp, thms_popup, editthms;

  XtAppContext helptool;

/* ************************************************************************ */
/* ******************************** MAIN ********************************** */
/* ************************************************************************ */

void main (argc, argv)
     int argc;
     char **argv;

{
  Arg         args[10];
  Cardinal    n;

  strcpy(help_path,"");
  strcpy(thms_path,"");

  /* first set up the window */

  holapropos = XtAppInitialize(&helptool, "xholhelp", NULL, ZERO, &argc,
                               argv, fallback_resources, NULL, ZERO);

  outer = XtCreateManagedWidget("frame", panedWidgetClass, holapropos,
				NULL, ZERO);

  /* dialog box and associated buttons */

  dialog = XtCreateManagedWidget("dialog", dialogWidgetClass,
                                 outer, NULL, ZERO);

  quit = XtCreateManagedWidget( "quit", commandWidgetClass,
                               dialog, NULL, ZERO);
  XtAddCallback( quit, XtNcallback, Quit, NULL);


  help = XtCreateManagedWidget( "help", commandWidgetClass,
                               dialog, NULL, ZERO);
  XtAddCallback( help, XtNcallback, Help, NULL);


  apropos = XtCreateManagedWidget( "apropos", commandWidgetClass,
                                  dialog, NULL, ZERO);
  XtAddCallback( apropos, XtNcallback, doA, NULL);


  entry = XtCreateManagedWidget( "reference", commandWidgetClass,
                                dialog, NULL, ZERO);
  XtAddCallback( entry, XtNcallback, doR, NULL);

  theorems = XtCreateManagedWidget( "theorems", commandWidgetClass,
                                   dialog, NULL, ZERO);

  /* Added CallBack later on... */

  clear = XtCreateManagedWidget( "clear", commandWidgetClass,
                                dialog, NULL, ZERO);
  XtAddCallback( clear, XtNcallback, ClearD, NULL);

  scrollf = XtCreateManagedWidget( "forward", commandWidgetClass,
                                dialog, NULL, ZERO);
  XtAddCallback( scrollf, XtNcallback, ScrollF, NULL);

  scrollb = XtCreateManagedWidget( "backward", commandWidgetClass,
                                dialog, NULL, ZERO);
  XtAddCallback( scrollb, XtNcallback, ScrollB, NULL);

  printout = XtCreateManagedWidget( "print", commandWidgetClass,
                                dialog, NULL, ZERO);
  XtAddCallback( printout, XtNcallback, PrintOut, NULL);

/*===========================================================================*/
/*            set up popup dialog boxes for editing help_paths               */
/*                                                                           */
/* help_popup:                                                               */
/*   ok       commits changes made to the path and pops down the winow.      */
/*            (<Key>Return accelerator)                                      */
/*   cancel   cancels the command and pops down the window.                  */
/*                                                                           */
/*                                                                           */
/* thms_popup:                                                               */
/*   ok       commits changes made to the path and pops down the window      */
/*            (<Key>Return accelerator)                                      */
/*   cancel   cancels the command and pops down the window.                  */
/*                                                                           */
/*===========================================================================*/

  pathedit = XtCreateManagedWidget( "pathedit", commandWidgetClass,
                                   dialog, NULL, ZERO);
  
  help_popup = XtCreatePopupShell( "help_popup", transientShellWidgetClass, 
                                  pathedit, NULL, ZERO);

  XtAddCallback( pathedit, XtNcallback, Popup, (XtPointer) help_popup);

  /*\ 
  |*| The popup will contain a dialog box, prompting the user for input. 
  |*| This dialog box will be resizable, loaded with the current path value.
  \*/

  n = 0;
  XtSetArg(args[n], XtNvalue, help_path);             n++;

  edithelp = XtCreateManagedWidget( "edithelp", dialogWidgetClass, help_popup, 
                                    args, n);

  XawDialogAddButton(edithelp, "ok", Update, (XtPointer) edithelp);
  XawDialogAddButton(edithelp, "cancel", Cancel, (XtPointer) edithelp);


  thms_popup= XtCreatePopupShell("thms_popup", transientShellWidgetClass, 
				 theorems, NULL, ZERO);

  /*\
  |*| Here's the callback function for the "theorems" button. The callback
  |*| is Popup which causes the dialog box to appear; popup needs to know
  |*| which popup to popup. Hope that's clear!
  \*/

  XtAddCallback( theorems, XtNcallback, Popup, (XtPointer) thms_popup);

  n = 0;
  XtSetArg(args[n], XtNvalue, thms_path);              n++;

  editthms = XtCreateManagedWidget( "editthms", dialogWidgetClass, thms_popup, 
                                    args, n);

  XawDialogAddButton(editthms, "ok", Update, (XtPointer) editthms);
  XawDialogAddButton(editthms, "cancel", Cancel, (XtPointer) editthms);

/*===========================================================================*/

/* text box, for output -- initially displays the contents of the HELPILE */

  n=0;
  XtSetArg(args[n], XtNtype, XawAsciiFile);            n++;
  XtSetArg(args[n], XtNstring, (XtArgVal) HELPFILE);   n++;

  alltext = XtCreateManagedWidget("text", asciiTextWidgetClass,
                                  outer, args, n);


/* infinite loop */

  XtAppAddActions(helptool, actionTable, XtNumber(actionTable));
  XtSetKeyboardFocus(outer,dialog);
  XtSetKeyboardFocus(help_popup,edithelp);
  XtSetKeyboardFocus(thms_popup,editthms);
  XtRealizeWidget(holapropos);

  XtAppMainLoop(helptool);
}

/* ************************************************************************* */
/* ***************************** HANDLERS & SUCH *************************** */
/* ************************************************************************* */

void Quit()
{
  XtDestroyApplicationContext(helptool); 
  exit(0);
}

void ClearD()
{
  Arg wargs[10];

  XtSetArg(wargs[0], XtNvalue, "");
  XtSetValues(dialog, wargs, 1);

}

void doA()
{
  char callsed[BUFSIZ], tempd[BUFSIZ];
  FILE *fin, *popen();
  
  strcpy(tempd, XawDialogGetValueString(dialog));

  busyCursor();

  strcpy(callsed, BIN);

  if (strlen(tempd) == 0)
    {
      strcat(callsed, "hol_funs ");    
      strcat(callsed, help_path);   /* 1st param is our internal help path */
    }
  else
    {
      strcat(callsed, "hol_apro ");
      strcat(callsed, tempd);       /* NB If blank get ALL 2 line synopses */
      strcat(callsed, " ");
      strcat(callsed, help_path);   /* 2nd param is our internal help path */
    }
  if ((fin = popen(callsed,"r")) == NULL)
    {
      fprintf(stderr, "cant run"); exit(1);
    }

  ShowData(fin);

  unbusyCursor();

  if (pclose(fin) == -1) fprintf (stderr, "didnt close\n");

} /* End of doA() */


void doR()
{
  char callsed[BUFSIZ], tempd[BUFSIZ];
  FILE *fin, *popen();

  strcpy(tempd, XawDialogGetValueString(dialog));

  if (strlen(tempd) == 0)
    {
      Arg wargs[10];
      XtDestroyWidget(alltext);
      XtSetArg(wargs[0], XtNtype, XawAsciiString);
      XtSetArg(wargs[1], XtNstring, (XtArgVal) EMPTY_DIALOG);
      alltext =  XtCreateManagedWidget("text", asciiTextWidgetClass,
				       outer, wargs, 2) ;
      return;
    }

  busyCursor();

  strcpy(callsed, BIN);
  strcat(callsed, "hol_ref ");
  strcat(callsed, tempd);
  strcat(callsed, " ");
  strcat(callsed, help_path);   /* 2nd param is our internal help path */

  if ((fin = popen(callsed,"r")) == NULL)
    {
      fprintf(stderr, "cant run"); exit(1);
    }
  
  ShowData(fin);

  unbusyCursor();

  if (pclose(fin) == -1) fprintf (stderr, "didnt close\n");

} /* End of doR() */

void doT()
{

  char callsed[BUFSIZ];
  FILE *fin, *popen();

  busyCursor();

  strcpy(callsed, BIN);
  strcat(callsed, "hol_thm \"");
  strcat(callsed,  XawDialogGetValueString(dialog));
  strcat(callsed, "\" ");
  strcat(callsed, thms_path);   /* 2nd param is our internal help path */


  if ((fin = popen(callsed,"r")) == NULL)
    {
      fprintf(stderr, "cant run"); 
      return;
    }

  ShowData(fin);
  unbusyCursor();

  if (pclose(fin) == -1) fprintf (stderr, "didnt close\n");

} /* End of doT() */


void PrintOut()
{
  char callshell[BUFSIZ];
  FILE *fin, *popen();
  Arg wargs[1];
  char *data;

  XtSetArg (wargs[0], XtNstring, &data);
  XtGetValues (XawTextGetSource (alltext), wargs, 1);


  if (getenv("HOL_PRINT_CMD") != NULL)
    {
      strcpy(callshell, getenv("HOL_PRINT_CMD"));
      if ((fin = popen(callshell,"w")) == NULL)
	{
          fprintf(stderr, "cant run"); 
          return;
	}
      fprintf(fin, "%s\n", data);
      if (pclose(fin) == -1)
	fprintf (stderr, "didnt close\n");
    }

} /* End of PrintData() -- Needs a dialog box! */

void Help()
{ 
  Arg wargs[1];

  XtDestroyWidget(alltext);

  XtSetArg(wargs[0], XtNstring, (XtArgVal) HELPFILE);

  alltext = XtCreateManagedWidget("text", asciiTextWidgetClass,
                                  outer, wargs, 1) ;
}

void ScrollF()
{
  XtCallActionProc(alltext, "next-page", 0, 0, 0);
  return;
}

void ScrollB()
{
  XtCallActionProc(alltext, "previous-page", 0, 0, 0);
  return;
}

void Popup(button, client_data, other)
     Widget button;
     XtPointer client_data, other;
{
  String name= XtName(button);

  if (strcmp(name,XtName(theorems)) == 0)
    {
      XtPopup(thms_popup, XtGrabNone);
    }
  else
    {
      XtPopup((Widget) client_data, XtGrabNone);
    }
}

void Cancel(button, dialog_box, dummy)
     Widget button;                    /* button pressed in dialog box */
     XtPointer dialog_box, dummy;      /* the dialog box calcelled     */
{
  Arg      args[10];
  Cardinal n;
  String   name = XtName((Widget) dialog_box);

  Widget popup = XtParent((Widget) dialog_box);

  XtPopdown(popup);

  n=0;
  if (strcmp(name,(XtName(editthms))) == 0)
    {
      XtSetArg(args[n], XtNvalue, thms_path);
    }
  else
    {
      XtSetArg(args[n], XtNvalue, help_path);
    }

  XtSetValues((Widget) dialog_box, args, ONE);

} /* End of Cancel() */

/* Go is the 'ActionProc' invoked when RETURN is pressed in dialog box */

void Go(widget, event, params, num_params)
     Widget widget;                     /* widget from whence it came */
     XEvent *event;		        /* the event <Key>Return      */
     String *params;	                /* Theses params are ignored  */
     Cardinal *num_params;
{
  Widget dialog= XtParent(widget);

  /* Just update the value of the path associated with this dialog */

  Update(widget, (XtPointer) dialog, (XtPointer) NULL);
}

void Update(button, dialog_box, other)
     Widget button;                   /* widget from whence it came   */
     XtPointer dialog_box, other;     /* the dialog box being updated */
{
  /* First figure out which popup this is all about */

  Widget popup    = XtParent((Widget) dialog_box);
  String new_path = XawDialogGetValueString((Widget) dialog_box);
  String name     = XtName((Widget) dialog_box);

  if (strcmp(name,(XtName(editthms))) == 0)
    {
      strcpy(thms_path, new_path);
    }
  else
    {
      strcpy(help_path, new_path);
    }

    XtPopdown(popup);
} /*End of Update() */

/* ************************************************************************* */
/* ************************* Auxiliary Functions *************************** */
/* ************************************************************************* */

void ShowData(file)
     FILE *file;
{
  char *data;           /* pointer to the data stored in dynamic memory */
  int num_bufs;
  char eachstring[MAXLEN];
  Arg wargs[10];

  /*  char new_data; */

  XtDestroyWidget(alltext);
  XtSetArg(wargs[0], XtNtype, XawAsciiString);

  /*
   * Get file size and allocate a chunk of memory for the file to be 
   * copied into.
   */

  if ((data = (char *)malloc(BUFSIZ)) == NULL)
    {
      XtSetArg(wargs[1], XtNstring, (XtArgVal) NOT_ENUF);
      alltext =  XtCreateManagedWidget("text", asciiTextWidgetClass,
                                       outer, wargs, 2) ;
      return;
    }

  num_bufs = 1;
  strcpy(data,"");
  
  while (fgets (eachstring, MAXLEN, file) != NULL)
    {
      if (strlen(data) + strlen(eachstring) > (num_bufs * BUFSIZ))
        if ((data = (char *)realloc(data, (BUFSIZ * ++num_bufs))) == NULL)
          {
            XtSetArg(wargs[1], XtNstring, (XtArgVal) NOT_ENUF);
            alltext =  XtCreateManagedWidget("text", asciiTextWidgetClass,
                                             outer, wargs, 2) ;
            return;
          }
      strcat(data, eachstring);
    }

  /*\ 
  |*| 
  |*| bug when data is of less than 500 bytes ?!?!?!
  |*| 
  \*/

  /* strcat(data,"\n");
   strcat(data,"   \n");  */

  /* if (strlen(data) < BUFSIZ) */
  
  /* new_data = XtNewString(data);  */

  XtSetArg(wargs[1], XtNstring, (XtArgVal)/* new_*/ data);
  
  alltext =  XtCreateManagedWidget("text", asciiTextWidgetClass,
                                   outer, wargs, 2) ;
  strcpy(data,"");

}/* End of ShowData() */

void busyCursor()
{
  static Cursor busyCursor = (Cursor) 0;
    
  /* define an appropriate busy cursor */
  
  busyCursor = XCreateFontCursor(XtDisplay(holapropos), XC_watch);

  XDefineCursor(XtDisplay(holapropos), XtWindow(dialog), busyCursor);
  XDefineCursor(XtDisplay(holapropos), XtWindow(alltext), busyCursor);
  XFlush(XtDisplay(holapropos));
    
  return;
}


void unbusyCursor()
{
  static Cursor unBusyCursor = (Cursor) 0;
  static Cursor textCursor = (Cursor) 0;

  unBusyCursor = XCreateFontCursor(XtDisplay(holapropos), XC_left_ptr);
  textCursor = XCreateFontCursor(XtDisplay(holapropos), XC_xterm);

  XDefineCursor(XtDisplay(holapropos), XtWindow(dialog), unBusyCursor);
  XDefineCursor(XtDisplay(holapropos), XtWindow(alltext), textCursor);
  XFlush(XtDisplay(holapropos));
    
  return;
}

