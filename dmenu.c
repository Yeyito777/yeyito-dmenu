/* See LICENSE file for copyright and license details. */
#include <ctype.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>
#include <unistd.h>

#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xutil.h>
#include <X11/extensions/XTest.h>
#ifdef XINERAMA
#include <X11/extensions/Xinerama.h>
#endif
#include <X11/Xft/Xft.h>

#include "drw.h"
#include "util.h"

/* macros */
#define INTERSECT(x,y,w,h,r)  (MAX(0, MIN((x)+(w),(r).x_org+(r).width)  - MAX((x),(r).x_org)) \
                             * MAX(0, MIN((y)+(h),(r).y_org+(r).height) - MAX((y),(r).y_org)))
#define TEXTW(X)              (drw_fontset_getwidth(drw, (X)) + lrpad)

/* enums */
enum { SchemeNorm, SchemeSel, SchemeOut, SchemeCursor, SchemeSuffix, SchemeLast }; /* color schemes */

struct item {
	char *text;
	struct item *left, *right;
	int out;
};

typedef struct {
	KeySym ksym;
	unsigned int state;
} Key;

static char text[BUFSIZ] = "";
static char *embed;
static const char *suffix = NULL;
static int bh, mw, mh;
static int inputw = 0, promptw;
static int lrpad; /* sum of left and right padding */
static size_t cursor;
static struct item *items = NULL;
static struct item *matches, *matchend;
static struct item *prev, *curr, *next, *sel;
static int mon = -1, screen;
static unsigned int using_vi_mode = 0;
static unsigned int truncate_len = 0;
static KeyCode replaykeycode;       /* pending Mod4 handoff keycode */
static KeySym replaykeysym = NoSymbol;
static int keyboardreleased;        /* handoff temporarily released grab */

static Atom clip, utf8;
static Display *dpy;
static Window root, parentwin, win;
static XIC xic;

static Drw *drw;
static Clr *scheme[SchemeLast];

#include "config.h"

static int (*fstrncmp)(const char *, const char *, size_t) = strncmp;
static char *(*fstrstr)(const char *, const char *) = strstr;
static int caseinsensitive = 0;
static int fuzzy = 0;

static void cleanup(void);
static void grabfocus(void);
static void qrselection(void);

static const char *handoffclasses[] = { "draw", "xcolor" };

static int
windowhasclass(Window w, const char *class)
{
	XClassHint ch = {0};
	int match = 0;

	if (!w || w == None || w == PointerRoot || w == root)
		return 0;
	if (XGetClassHint(dpy, w, &ch)) {
		match = (ch.res_class && strcmp(ch.res_class, class) == 0);
		if (ch.res_name)
			XFree(ch.res_name);
		if (ch.res_class)
			XFree(ch.res_class);
	}
	return match;
}

static int
windowhasanyclass(Window w, const char *classes[], size_t n)
{
	size_t i;

	for (i = 0; i < n; i++)
		if (windowhasclass(w, classes[i]))
			return 1;
	return 0;
}

static void
clearreplay(void)
{
	replaykeycode = 0;
	replaykeysym = NoSymbol;
}

static int
trygrabkeyboard(void)
{
	return XGrabKeyboard(dpy, DefaultRootWindow(dpy), True, GrabModeAsync,
	                     GrabModeAsync, CurrentTime) == GrabSuccess;
}

static void
restorehandoff(void)
{
	Window focuswin;
	int revertwin;

	if (!keyboardreleased)
		return;
	XGetInputFocus(dpy, &focuswin, &revertwin);
	if (focuswin != win) {
		if (windowhasclass(focuswin, "dmenu")) {
			cleanup();
			exit(1);
		}
		if (windowhasanyclass(focuswin, handoffclasses, LENGTH(handoffclasses)))
			return;
	}
	if (!trygrabkeyboard())
		return;
	keyboardreleased = 0;
	grabfocus();
}

static unsigned int
textw_clamp(const char *str, unsigned int n)
{
	unsigned int w = drw_fontset_getwidth_clamp(drw, str, n) + lrpad;
	return MIN(w, n);
}

static void
appenditem(struct item *item, struct item **list, struct item **last)
{
	if (*last)
		(*last)->right = item;
	else
		*list = item;

	item->left = *last;
	item->right = NULL;
	*last = item;
}

static const char *
displaytext(const char *text, char *buf, size_t bufsz)
{
	if (!truncate_len || strlen(text) <= truncate_len)
		return text;
	snprintf(buf, bufsz, "%.*s...", (int)truncate_len, text);
	return buf;
}

static void
calcoffsets(void)
{
	char buf[BUFSIZ];
	int i, n;

	if (lines > 0)
		n = lines * bh;
	else
		n = mw - (promptw + inputw + TEXTW("<") + TEXTW(">"));
	/* calculate which items will begin the next page and previous page */
	for (i = 0, next = curr; next; next = next->right)
		if ((i += (lines > 0) ? bh : textw_clamp(displaytext(next->text, buf, sizeof buf), n)) > n)
			break;
	for (i = 0, prev = curr; prev && prev->left; prev = prev->left)
		if ((i += (lines > 0) ? bh : textw_clamp(displaytext(prev->left->text, buf, sizeof buf), n)) > n)
			break;
}

static void
cleanup(void)
{
	size_t i;

	XUngrabKeyboard(dpy, CurrentTime);
	for (i = 0; i < SchemeLast; i++)
		free(scheme[i]);
	for (i = 0; items && items[i].text; ++i)
		free(items[i].text);
	free(items);
	drw_free(drw);
	XSync(dpy, False);
	XCloseDisplay(dpy);
}

static void
qrselection(void)
{
	const char *src = (sel && sel->text) ? sel->text : text;
	char *choice;

	if (!src || !*src)
		return;
	if (!(choice = strdup(src)))
		die("strdup:");

	cleanup();
	execlp("qr", "qr", choice, (char *)NULL);
	die("qr:");
}

static int
iswmkeysym(KeySym ksym)
{
	switch (ksym) {
	case XK_Super_L:
	case XK_Super_R:
	case XK_Hyper_L:
	case XK_Hyper_R:
	case XK_Meta_L:
	case XK_Meta_R:
	case XK_Shift_L:
	case XK_Shift_R:
	case XK_Control_L:
	case XK_Control_R:
	case XK_Alt_L:
	case XK_Alt_R:
		return 0;
	default:
		return 1;
	}
}

static int
keyisdown(Display *dpy, KeyCode code)
{
	char keys[32];

	if (!code)
		return 0;
	XQueryKeymap(dpy, keys);
	return !!(keys[code / 8] & (1 << (code % 8)));
}

static KeyCode
mod4keycode(Display *dpy, int preferup)
{
	static KeySym mod4syms[] = {
		XK_Super_L, XK_Super_R,
		XK_Hyper_L, XK_Hyper_R,
		XK_Meta_L,  XK_Meta_R,
	};
	XModifierKeymap *modmap;
	KeyCode code, fallback = 0;
	int i, start, end;
	size_t j;

	if ((modmap = XGetModifierMapping(dpy))) {
		start = Mod4MapIndex * modmap->max_keypermod;
		end = start + modmap->max_keypermod;
		for (i = start; i < end; i++) {
			code = modmap->modifiermap[i];
			if (!code)
				continue;
			if (!fallback)
				fallback = code;
			if (!preferup || !keyisdown(dpy, code)) {
				XFreeModifiermap(modmap);
				return code;
			}
		}
		XFreeModifiermap(modmap);
	}
	if (fallback && (!preferup || !keyisdown(dpy, fallback)))
		return fallback;
	for (j = 0; j < LENGTH(mod4syms); j++) {
		code = XKeysymToKeycode(dpy, mod4syms[j]);
		if (code && (!preferup || !keyisdown(dpy, code)))
			return code;
	}
	return 0;
}

static void
replaywmkey(KeyCode keycode, KeySym ksym)
{
	Display *rdpy;
	KeyCode mod4, heldmod4;

	if (!keycode || !iswmkeysym(ksym))
		return;
	if (!(rdpy = XOpenDisplay(NULL)))
		return;

	/*
	 * dmenu already consumed the original Mod4 combo under its active keyboard
	 * grab. After closing dmenu, synthesize a fresh Mod4 combo that dwm can see.
	 * Prefer a Mod4 keycode that is not currently held physically, so we get a
	 * true new modifier press edge.
	 */
	usleep(20000);
	heldmod4 = mod4keycode(rdpy, 0);
	mod4 = mod4keycode(rdpy, 1);
	if (!mod4)
		mod4 = heldmod4;
	if (!mod4) {
		XCloseDisplay(rdpy);
		return;
	}

	if (mod4 == heldmod4 && keyisdown(rdpy, mod4)) {
		XTestFakeKeyEvent(rdpy, mod4, False, CurrentTime);
		XSync(rdpy, False);
		usleep(15000);
	}
	XTestFakeKeyEvent(rdpy, mod4, True, CurrentTime);
	XSync(rdpy, False);
	usleep(15000);
	XTestFakeKeyEvent(rdpy, keycode, True, CurrentTime);
	XSync(rdpy, False);
	usleep(15000);
	XTestFakeKeyEvent(rdpy, keycode, False, CurrentTime);
	XSync(rdpy, False);
	usleep(15000);
	XTestFakeKeyEvent(rdpy, mod4, False, CurrentTime);
	XSync(rdpy, False);
	XCloseDisplay(rdpy);
}

static char *
cistrstr(const char *h, const char *n)
{
	size_t i;

	if (!n[0])
		return (char *)h;

	for (; *h; ++h) {
		for (i = 0; n[i] && tolower((unsigned char)n[i]) ==
		            tolower((unsigned char)h[i]); ++i)
			;
		if (n[i] == '\0')
			return (char *)h;
	}
	return NULL;
}

static int
fuzzycharcmp(char a, char b)
{
	if (caseinsensitive)
		return tolower((unsigned char)a) == tolower((unsigned char)b);
	return a == b;
}

static int
fuzzymatch(const char *str, const char *pattern)
{
	if (!pattern[0])
		return 1;
	for (; *str && *pattern; str++)
		if (fuzzycharcmp(*str, *pattern))
			pattern++;
	return !*pattern;
}

static int
drawitem(struct item *item, int x, int y, int w)
{
	char buf[BUFSIZ];

	if (item == sel)
		drw_setscheme(drw, scheme[SchemeSel]);
	else if (item->out)
		drw_setscheme(drw, scheme[SchemeOut]);
	else
		drw_setscheme(drw, scheme[SchemeNorm]);

	return drw_text(drw, x, y, w, bh, lrpad / 2, displaytext(item->text, buf, sizeof buf), 0);
}

static void
drawmenu(void)
{
	unsigned int curpos;
	struct item *item;
	int x = 0, y = 0, w;

	drw_setscheme(drw, scheme[SchemeNorm]);
	drw_rect(drw, 0, 0, mw, mh, 1, 1);

	if (prompt && *prompt) {
		drw_setscheme(drw, scheme[SchemeSel]);
		x = drw_text(drw, x, 0, promptw, bh, lrpad / 2, prompt, 0);
	}
	/* draw input field */
	w = (lines > 0 || !matches) ? mw - x : inputw;
	drw_setscheme(drw, scheme[SchemeNorm]);
	drw_text(drw, x, 0, w, bh, lrpad / 2, text, 0);

	/* draw suffix hint (e.g. ".mp4") dimmed after input text */
	if (suffix) {
		int sx = x + drw_fontset_getwidth(drw, text) + lrpad / 2;
		drw_setscheme(drw, scheme[SchemeSuffix]);
		drw_text(drw, sx, 0, drw_fontset_getwidth(drw, suffix) + lrpad / 2, bh, 0, suffix, 0);
		drw_setscheme(drw, scheme[SchemeNorm]);
	}

	curpos = TEXTW(text) - TEXTW(&text[cursor]);
	curpos += lrpad / 2 - 1;
	if (using_vi_mode && text[0] != '\0') {
		drw_setscheme(drw, scheme[SchemeCursor]);
		char vi_char[] = {text[cursor], '\0'};
		drw_text(drw, x + curpos, 0, TEXTW(vi_char) - lrpad, bh, 0, vi_char, 0);
	} else if (using_vi_mode) {
		drw_setscheme(drw, scheme[SchemeCursor]);
		drw_rect(drw, x + curpos, 2, lrpad / 2, bh - 4, 1, 1);
	} else if (curpos < w) {
		drw_setscheme(drw, scheme[SchemeCursor]);
		drw_rect(drw, x + curpos, 2, 2, bh - 4, 1, 1);
	}

	if (lines > 0) {
		/* draw vertical list */
		for (item = curr; item != next; item = item->right)
			drawitem(item, x, y += bh, mw - x);
	} else if (matches) {
		/* draw horizontal list */
		x += inputw;
		w = TEXTW("<");
		if (curr->left) {
			drw_setscheme(drw, scheme[SchemeNorm]);
			drw_text(drw, x, 0, w, bh, lrpad / 2, "<", 0);
		}
		x += w;
		for (item = curr; item != next; item = item->right) {
			char buf[BUFSIZ];
			x = drawitem(item, x, 0, textw_clamp(displaytext(item->text, buf, sizeof buf), mw - x - TEXTW(">")));
		}
		if (next) {
			w = TEXTW(">");
			drw_setscheme(drw, scheme[SchemeNorm]);
			drw_text(drw, mw - w, 0, w, bh, lrpad / 2, ">", 0);
		}
	}
	drw_map(drw, win, 0, 0, mw, mh);
}

static void
grabfocus(void)
{
	struct timespec ts = { .tv_sec = 0, .tv_nsec = 10000000  };
	Window focuswin;
	int i, revertwin;

	for (i = 0; i < 100; ++i) {
		XGetInputFocus(dpy, &focuswin, &revertwin);
		if (focuswin == win)
			return;
		XSetInputFocus(dpy, win, RevertToParent, CurrentTime);
		nanosleep(&ts, NULL);
	}
	die("cannot grab focus");
}

static void
grabkeyboard(void)
{
	struct timespec ts = { .tv_sec = 0, .tv_nsec = 1000000  };
	int i;

	if (embed)
		return;
	/* try to grab keyboard, we may have to wait for another process to ungrab */
	for (i = 0; i < 1000; i++) {
		if (XGrabKeyboard(dpy, DefaultRootWindow(dpy), True, GrabModeAsync,
		                  GrabModeAsync, CurrentTime) == GrabSuccess)
			return;
		nanosleep(&ts, NULL);
	}
	die("cannot grab keyboard");
}

static void
match(void)
{
	static char **tokv = NULL;
	static int tokn = 0;

	char buf[sizeof text], *s;
	int i, tokc = 0;
	size_t len, textsize;
	struct item *item, *lprefix, *lsubstr, *lfuzzy, *prefixend, *substrend, *fuzzyend;

	strcpy(buf, text);
	/* separate input text into tokens to be matched individually */
	for (s = strtok(buf, " "); s; tokv[tokc - 1] = s, s = strtok(NULL, " "))
		if (++tokc > tokn && !(tokv = realloc(tokv, ++tokn * sizeof *tokv)))
			die("cannot realloc %zu bytes:", tokn * sizeof *tokv);
	len = tokc ? strlen(tokv[0]) : 0;

	matches = lprefix = lsubstr = lfuzzy = matchend = prefixend = substrend = fuzzyend = NULL;
	textsize = strlen(text) + 1;
	for (item = items; item && item->text; item++) {
		for (i = 0; i < tokc; i++)
			if (fuzzy ? !fuzzymatch(item->text, tokv[i]) : !fstrstr(item->text, tokv[i]))
				break;
		if (i != tokc) /* not all tokens match */
			continue;
		/* exact matches go first, then prefixes, then substrings, then fuzzy matches */
		if (!tokc || !fstrncmp(text, item->text, textsize))
			appenditem(item, &matches, &matchend);
		else if (!fstrncmp(tokv[0], item->text, len))
			appenditem(item, &lprefix, &prefixend);
		else if (fstrstr(item->text, tokv[0]))
			appenditem(item, &lsubstr, &substrend);
		else
			appenditem(item, &lfuzzy, &fuzzyend);
	}
	if (lprefix) {
		if (matches) {
			matchend->right = lprefix;
			lprefix->left = matchend;
		} else
			matches = lprefix;
		matchend = prefixend;
	}
	if (lsubstr) {
		if (matches) {
			matchend->right = lsubstr;
			lsubstr->left = matchend;
		} else
			matches = lsubstr;
		matchend = substrend;
	}
	if (lfuzzy) {
		if (matches) {
			matchend->right = lfuzzy;
			lfuzzy->left = matchend;
		} else
			matches = lfuzzy;
		matchend = fuzzyend;
	}
	curr = sel = matches;
	calcoffsets();
}

static void
insert(const char *str, ssize_t n)
{
	if (strlen(text) + n > sizeof text - 1)
		return;
	/* move existing text out of the way, insert new text, and update cursor */
	memmove(&text[cursor + n], &text[cursor], sizeof text - cursor - MAX(n, 0));
	if (n > 0)
		memcpy(&text[cursor], str, n);
	cursor += n;
	match();
}

static size_t
nextrune(int inc)
{
	ssize_t n;

	/* return location of next utf8 rune in the given direction (+1 or -1) */
	for (n = cursor + inc; n + inc >= 0 && (text[n] & 0xc0) == 0x80; n += inc)
		;
	return n;
}

static void
movewordedge(int dir)
{
	if (dir < 0) { /* move cursor to the start of the word*/
		while (cursor > 0 && strchr(worddelimiters, text[nextrune(-1)]))
			cursor = nextrune(-1);
		while (cursor > 0 && !strchr(worddelimiters, text[nextrune(-1)]))
			cursor = nextrune(-1);
	} else { /* move cursor to the end of the word */
		while (text[cursor] && strchr(worddelimiters, text[cursor]))
			cursor = nextrune(+1);
		while (text[cursor] && !strchr(worddelimiters, text[cursor]))
			cursor = nextrune(+1);
	}
}

static void
vi_keypress(KeySym ksym, const XKeyEvent *ev)
{
	static const size_t quit_len = LENGTH(quit_keys);
	if (ev->state & ControlMask) {
		switch(ksym) {
		/* movement */
		case XK_d: /* fallthrough */
			if (next) {
				sel = curr = next;
				calcoffsets();
				goto draw;
			} else
				ksym = XK_G;
			break;
		case XK_u:
			if (prev) {
				sel = curr = prev;
				calcoffsets();
				goto draw;
			} else
				ksym = XK_g;
			break;
		case XK_p: /* fallthrough */
		case XK_P: break;
		case XK_c:
			cleanup();
			exit(1);
		case XK_Return: /* fallthrough */
		case XK_KP_Enter: break;
		default: return;
		}
	}

	switch(ksym) {
	/* movement */
	case XK_0:
		cursor = 0;
		break;
	case XK_dollar:
		if (text[cursor + 1] != '\0') {
			cursor = strlen(text) - 1;
			break;
		}
		break;
	case XK_b:
		movewordedge(-1);
		break;
	case XK_e:
		cursor = nextrune(+1);
		movewordedge(+1);
		if (text[cursor] == '\0')
			--cursor;
		else
			cursor = nextrune(-1);
		break;
	case XK_g:
		if (sel == matches) {
			break;
		}
		sel = curr = matches;
		calcoffsets();
		break;
	case XK_G:
		if (next) {
			/* jump to end of list and position items in reverse */
			curr = matchend;
			calcoffsets();
			curr = prev;
			calcoffsets();
			while (next && (curr = curr->right))
				calcoffsets();
		}
		sel = matchend;
		break;
	case XK_h:
		if (cursor)
			cursor = nextrune(-1);
		break;
	case XK_j:
		if (sel && sel->right && (sel = sel->right) == next) {
			curr = next;
			calcoffsets();
		}
		break;
	case XK_k:
		if (sel && sel->left && (sel = sel->left)->right == curr) {
			curr = prev;
			calcoffsets();
		}
		break;
	case XK_l:
		if (text[cursor] != '\0' && text[cursor + 1] != '\0')
			cursor = nextrune(+1);
		else if (text[cursor] == '\0' && cursor)
			--cursor;
		break;
	case XK_w:
		movewordedge(+1);
		if (text[cursor] != '\0' && text[cursor + 1] != '\0')
			cursor = nextrune(+1);
		else if (cursor)
			--cursor;
		break;
	/* insertion */
	case XK_a:
		cursor = nextrune(+1);
		/* fallthrough */
	case XK_i:
		using_vi_mode = 0;
		break;
	case XK_A:
		if (text[cursor] != '\0')
			cursor = strlen(text);
		using_vi_mode = 0;
		break;
	case XK_I:
		cursor = using_vi_mode = 0;
		break;
	case XK_p:
		if (text[cursor] != '\0')
			cursor = nextrune(+1);
		XConvertSelection(dpy, (ev->state & ControlMask) ? clip : XA_PRIMARY,
							utf8, utf8, win, CurrentTime);
		return;
	case XK_P:
		XConvertSelection(dpy, (ev->state & ControlMask) ? clip : XA_PRIMARY,
							utf8, utf8, win, CurrentTime);
		return;
	/* deletion */
	case XK_D:
		text[cursor] = '\0';
		if (cursor)
			cursor = nextrune(-1);
		match();
		break;
	case XK_x:
		cursor = nextrune(+1);
		insert(NULL, nextrune(-1) - cursor);
		if (text[cursor] == '\0' && text[0] != '\0')
			--cursor;
		match();
		break;
	/* misc. */
	case XK_Return:
	case XK_KP_Enter:
		puts((sel && !(ev->state & ShiftMask)) ? sel->text : text);
		if (!(ev->state & ControlMask)) {
			cleanup();
			exit(0);
		}
		if (sel)
			sel->out = 1;
		break;
	case XK_Tab:
		if (!sel)
			return;
		strncpy(text, sel->text, sizeof text - 1);
		text[sizeof text - 1] = '\0';
		cursor = strlen(text) - 1;
		match();
		break;
	case XK_q:
		qrselection();
		break;
	default:
		for (size_t i = 0; i < quit_len; ++i)
			if (quit_keys[i].ksym == ksym &&
				(quit_keys[i].state & ev->state) == quit_keys[i].state) {
				cleanup();
				exit(1);
			}
	}

draw:
	drawmenu();
}

static void
keyrelease(XKeyEvent *ev)
{
	XEvent next;
	KeyCode keycode;
	KeySym ksym;

	if (!replaykeycode || ev->keycode != replaykeycode)
		return;
	/* suppress autorepeat-generated releases */
	if (XPending(dpy)) {
		XPeekEvent(dpy, &next);
		if (next.type == KeyPress &&
		    next.xkey.time == ev->time &&
		    next.xkey.keycode == ev->keycode)
			return;
	}
	keycode = replaykeycode;
	ksym = replaykeysym;
	clearreplay();
	XUngrabKeyboard(dpy, CurrentTime);
	keyboardreleased = 1;
	XSync(dpy, False);
	replaywmkey(keycode, ksym);
}

static void
keypress(XKeyEvent *ev)
{
	char buf[64];
	int len;
	KeySym ksym = NoSymbol;
	Status status;

	len = XmbLookupString(xic, ev, buf, sizeof buf, &ksym, &status);
	switch (status) {
	default: /* XLookupNone, XBufferOverflow */
		return;
	case XLookupChars: /* composed string from input method */
		goto insert;
	case XLookupKeySym:
	case XLookupBoth: /* a KeySym and a string are returned: use keysym */
		break;
	}

	if ((ev->state & Mod4Mask) && iswmkeysym(ksym)) {
		replaykeycode = ev->keycode;
		replaykeysym = ksym;
		keyboardreleased = 0;
		return;
	}

	if (using_vi_mode) {
		vi_keypress(ksym, ev);
		return;
	} else if (vi_mode &&
			   (ksym == global_esc.ksym &&
				(ev->state & global_esc.state) == global_esc.state)) {
		using_vi_mode = 1;
		if (cursor)
			cursor = nextrune(-1);
		goto draw;
	}

	if (ev->state & ControlMask) {
		switch(ksym) {
		case XK_a: ksym = XK_Home;      break;
		case XK_b: ksym = XK_Left;      break;
		case XK_c: ksym = XK_Escape;    break;
		case XK_d: ksym = XK_Delete;    break;
		case XK_e: ksym = XK_End;       break;
		case XK_f: ksym = XK_Right;     break;
		case XK_g: ksym = XK_Escape;    break;
		case XK_h: ksym = XK_BackSpace; break;
		case XK_i: ksym = XK_Tab;       break;
		case XK_j: /* fallthrough */
		case XK_J: /* fallthrough */
		case XK_m: /* fallthrough */
		case XK_M: ksym = XK_Return; ev->state &= ~ControlMask; break;
		case XK_n: ksym = XK_Down;      break;
		case XK_p: ksym = XK_Up;        break;

		case XK_k: /* delete right */
			text[cursor] = '\0';
			match();
			break;
		case XK_u: /* delete left */
			insert(NULL, 0 - cursor);
			break;
		case XK_w: /* delete word */
			while (cursor > 0 && strchr(worddelimiters, text[nextrune(-1)]))
				insert(NULL, nextrune(-1) - cursor);
			while (cursor > 0 && !strchr(worddelimiters, text[nextrune(-1)]))
				insert(NULL, nextrune(-1) - cursor);
			break;
		case XK_y: /* paste selection */
		case XK_Y:
			XConvertSelection(dpy, (ev->state & ShiftMask) ? clip : XA_PRIMARY,
			                  utf8, utf8, win, CurrentTime);
			return;
		case XK_Left:
		case XK_KP_Left:
			movewordedge(-1);
			goto draw;
		case XK_Right:
		case XK_KP_Right:
			movewordedge(+1);
			goto draw;
		case XK_Return:
		case XK_KP_Enter:
			break;
		case XK_bracketleft:
			cleanup();
			exit(1);
		default:
			return;
		}
	} else if (ev->state & Mod1Mask) {
		switch(ksym) {
		case XK_b:
			movewordedge(-1);
			goto draw;
		case XK_f:
			movewordedge(+1);
			goto draw;
		case XK_g: ksym = XK_Home;  break;
		case XK_G: ksym = XK_End;   break;
		case XK_h: ksym = XK_Up;    break;
		case XK_j: ksym = XK_Next;  break;
		case XK_k: ksym = XK_Prior; break;
		case XK_l: ksym = XK_Down;  break;
		default:
			return;
		}
	}

	switch(ksym) {
	default:
insert:
		if (!iscntrl((unsigned char)*buf))
			insert(buf, len);
		break;
	case XK_Delete:
	case XK_KP_Delete:
		if (text[cursor] == '\0')
			return;
		cursor = nextrune(+1);
		/* fallthrough */
	case XK_BackSpace:
		if (cursor == 0)
			return;
		insert(NULL, nextrune(-1) - cursor);
		break;
	case XK_End:
	case XK_KP_End:
		if (text[cursor] != '\0') {
			cursor = strlen(text);
			break;
		}
		if (next) {
			/* jump to end of list and position items in reverse */
			curr = matchend;
			calcoffsets();
			curr = prev;
			calcoffsets();
			while (next && (curr = curr->right))
				calcoffsets();
		}
		sel = matchend;
		break;
	case XK_Escape:
		cleanup();
		exit(1);
	case XK_Home:
	case XK_KP_Home:
		if (sel == matches) {
			cursor = 0;
			break;
		}
		sel = curr = matches;
		calcoffsets();
		break;
	case XK_Left:
	case XK_KP_Left:
		if (cursor > 0 && (!sel || !sel->left || lines > 0)) {
			cursor = nextrune(-1);
			break;
		}
		if (lines > 0)
			return;
		/* fallthrough */
	case XK_Up:
	case XK_KP_Up:
		if (sel && sel->left && (sel = sel->left)->right == curr) {
			curr = prev;
			calcoffsets();
		}
		break;
	case XK_Next:
	case XK_KP_Next:
		if (!next)
			return;
		sel = curr = next;
		calcoffsets();
		break;
	case XK_Prior:
	case XK_KP_Prior:
		if (!prev)
			return;
		sel = curr = prev;
		calcoffsets();
		break;
	case XK_Return:
	case XK_KP_Enter:
		puts((sel && !(ev->state & ShiftMask)) ? sel->text : text);
		if (!(ev->state & ControlMask)) {
			cleanup();
			exit(0);
		}
		if (sel)
			sel->out = 1;
		break;
	case XK_Right:
	case XK_KP_Right:
		if (text[cursor] != '\0') {
			cursor = nextrune(+1);
			break;
		}
		if (lines > 0)
			return;
		/* fallthrough */
	case XK_Down:
	case XK_KP_Down:
		if (sel && sel->right && (sel = sel->right) == next) {
			curr = next;
			calcoffsets();
		}
		break;
	case XK_Tab:
		if (!sel)
			return;
		cursor = strnlen(sel->text, sizeof text - 1);
		memcpy(text, sel->text, cursor);
		text[cursor] = '\0';
		match();
		break;
	}

draw:
	drawmenu();
}

static void
paste(void)
{
	char *p, *q;
	int di;
	unsigned long dl;
	Atom da;

	/* we have been given the current selection, now insert it into input */
	if (XGetWindowProperty(dpy, win, utf8, 0, (sizeof text / 4) + 1, False,
	                   utf8, &da, &di, &dl, &dl, (unsigned char **)&p)
	    == Success && p) {
		insert(p, (q = strchr(p, '\n')) ? q - p : (ssize_t)strlen(p));
		XFree(p);
	}
	if (using_vi_mode && text[cursor] == '\0')
		--cursor;
	drawmenu();
}

static void
readstdin(void)
{
	char *line = NULL;
	size_t i, itemsiz = 0, linesiz = 0;
	ssize_t len;

	/* read each line from stdin and add it to the item list */
	for (i = 0; (len = getline(&line, &linesiz, stdin)) != -1; i++) {
		if (i + 1 >= itemsiz) {
			itemsiz += 256;
			if (!(items = realloc(items, itemsiz * sizeof(*items))))
				die("cannot realloc %zu bytes:", itemsiz * sizeof(*items));
		}
		if (line[len - 1] == '\n')
			line[len - 1] = '\0';
		if (!(items[i].text = strdup(line)))
			die("strdup:");

		items[i].out = 0;
	}
	free(line);
	if (items)
		items[i].text = NULL;
	lines = MIN(lines, i);
}

static void
run(void)
{
	XEvent ev;

	int xfd = ConnectionNumber(dpy);

	for (;;) {
		while (XPending(dpy)) {
			XNextEvent(dpy, &ev);
			if (XFilterEvent(&ev, win))
				continue;
			switch(ev.type) {
			case DestroyNotify:
				if (ev.xdestroywindow.window != win)
					break;
				cleanup();
				exit(1);
			case Expose:
				if (ev.xexpose.count == 0)
					drw_map(drw, win, 0, 0, mw, mh);
				break;
			case FocusIn:
				if (keyboardreleased) {
					grabkeyboard();
					keyboardreleased = 0;
				}
				/* regrab focus from parent window */
				if (ev.xfocus.window != win)
					grabfocus();
				break;
			case KeyPress:
				keypress(&ev.xkey);
				break;
			case KeyRelease:
				keyrelease(&ev.xkey);
				break;
			case SelectionNotify:
				if (ev.xselection.property == utf8)
					paste();
				break;
			case VisibilityNotify:
				if (ev.xvisibility.state != VisibilityUnobscured)
					XRaiseWindow(dpy, win);
				break;
			}
		}
		restorehandoff();
		{
			fd_set fds;
			struct timeval tv = { .tv_sec = 0, .tv_usec = 50000 };
			FD_ZERO(&fds);
			FD_SET(xfd, &fds);
			select(xfd + 1, &fds, NULL, NULL, &tv);
		}
	}
}

static int
max_textw(void)
{
	char buf[BUFSIZ];
	int len = 0;
	for (struct item *item = items; item && item->text; item++)
		len = MAX(TEXTW(displaytext(item->text, buf, sizeof buf)), len);
	return len;
}

static void
setup(void)
{
	int x, y, i, j;
	unsigned int du;
	XSetWindowAttributes swa;
	XIM xim;
	Window w, dw, *dws;
	XWindowAttributes wa;
	XClassHint ch = {"dmenu", "dmenu"};
#ifdef XINERAMA
	XineramaScreenInfo *info;
	Window pw;
	int a, di, n, area = 0;
#endif
	/* init appearance */
	for (j = 0; j < SchemeLast; j++)
		scheme[j] = drw_scm_create(drw, colors[j], 2);

	clip = XInternAtom(dpy, "CLIPBOARD",   False);
	utf8 = XInternAtom(dpy, "UTF8_STRING", False);

	/* calculate menu geometry */
	bh = drw->fonts->h + 2;
	lines = MAX(lines, 0);
	mh = (lines + 1) * bh;
#ifdef XINERAMA
	i = 0;
	if (parentwin == root && (info = XineramaQueryScreens(dpy, &n))) {
		XGetInputFocus(dpy, &w, &di);
		if (mon >= 0 && mon < n)
			i = mon;
		else if (w != root && w != PointerRoot && w != None) {
			/* find top-level window containing current input focus */
			do {
				if (XQueryTree(dpy, (pw = w), &dw, &w, &dws, &du) && dws)
					XFree(dws);
			} while (w != root && w != pw);
			/* find xinerama screen with which the window intersects most */
			if (XGetWindowAttributes(dpy, pw, &wa))
				for (j = 0; j < n; j++)
					if ((a = INTERSECT(wa.x, wa.y, wa.width, wa.height, info[j])) > area) {
						area = a;
						i = j;
					}
		}
		/* no focused window is on screen, so use pointer location instead */
		if (mon < 0 && !area && XQueryPointer(dpy, root, &dw, &dw, &x, &y, &di, &di, &du))
			for (i = 0; i < n; i++)
				if (INTERSECT(x, y, 1, 1, info[i]) != 0)
					break;

		if (centered) {
			mw = MIN(MAX(max_textw() + promptw, min_width), info[i].width);
			x = info[i].x_org + ((info[i].width  - mw) / 2);
			y = info[i].y_org + ((info[i].height - mh) / 2);
		} else {
			x = info[i].x_org;
			y = info[i].y_org + (topbar ? 0 : info[i].height - mh);
			mw = info[i].width;
		}
		XFree(info);
	} else
#endif
	{
		if (!XGetWindowAttributes(dpy, parentwin, &wa))
			die("could not get embedding window attributes: 0x%lx",
			    parentwin);
		if (centered) {
			mw = MIN(MAX(max_textw() + promptw, min_width), wa.width);
			x = (wa.width  - mw) / 2;
			y = (wa.height - mh) / 2;
		} else {
			x = 0;
			y = topbar ? 0 : wa.height - mh;
			mw = wa.width;
		}
	}
	promptw = (prompt && *prompt) ? TEXTW(prompt) - lrpad / 4 : 0;
	inputw = mw / 3; /* input width: ~33% of monitor width */
	match();

	/* create menu window */
	swa.override_redirect = True;
	swa.background_pixel = scheme[SchemeNorm][ColBg].pixel;
	swa.event_mask = ExposureMask | KeyPressMask | KeyReleaseMask | VisibilityChangeMask;
	win = XCreateWindow(dpy, root, x, y, mw, mh, border_width,
	                    CopyFromParent, CopyFromParent, CopyFromParent,
	                    CWOverrideRedirect | CWBackPixel | CWEventMask, &swa);
	if (border_width) {
		XColor color;
		Colormap cmap = DefaultColormap(dpy, DefaultScreen(dpy));
		XAllocNamedColor(dpy, cmap, bordercolor, &color, &color);
		XSetWindowBorder(dpy, win, color.pixel);
	}
	XSetClassHint(dpy, win, &ch);

	/* input methods */
	if ((xim = XOpenIM(dpy, NULL, NULL, NULL)) == NULL)
		die("XOpenIM failed: could not open input device");

	xic = XCreateIC(xim, XNInputStyle, XIMPreeditNothing | XIMStatusNothing,
	                XNClientWindow, win, XNFocusWindow, win, NULL);

	XMapRaised(dpy, win);
	if (embed) {
		XReparentWindow(dpy, win, parentwin, x, y);
		XSelectInput(dpy, parentwin, FocusChangeMask | SubstructureNotifyMask);
		if (XQueryTree(dpy, parentwin, &dw, &w, &dws, &du) && dws) {
			for (i = 0; i < du && dws[i] != win; ++i)
				XSelectInput(dpy, dws[i], FocusChangeMask);
			XFree(dws);
		}
		grabfocus();
	}
	drw_resize(drw, mw, mh);
	drawmenu();
}

static void
usage(void)
{
	die("usage: dmenu [-bcfiFv] [-l lines] [-t chars] [-p prompt] [-fn font] [-m monitor]\n"
	    "             [-nb color] [-nf color] [-sb color] [-sf color] [-w windowid]");
}

int
main(int argc, char *argv[])
{
	XWindowAttributes wa;
	int i, fast = 0;

	for (i = 1; i < argc; i++)
		/* these options take no arguments */
		if (!strcmp(argv[i], "-v")) {      /* prints version information */
			puts("dmenu-"VERSION);
			exit(0);
		} else if (!strcmp(argv[i], "-b")) /* appears at the bottom of the screen */
			topbar = 0;
		else if (!strcmp(argv[i], "-f"))   /* grabs keyboard before reading stdin */
			fast = 1;
		else if (!strcmp(argv[i], "-i")) { /* case-insensitive item matching */
			fstrncmp = strncasecmp;
			fstrstr = cistrstr;
			caseinsensitive = 1;
		} else if (!strcmp(argv[i], "-F")) { /* fuzzy subsequence item matching */
			fuzzy = 1;
		} else if (!strcmp(argv[i], "-c"))   /* appears centered on screen */
			centered = 1;
		else if (!strcmp(argv[i], "-vi")) {
			vi_mode = 1;
			using_vi_mode = start_mode;
			global_esc.ksym = XK_Escape;
			global_esc.state = 0;
		} else if (i + 1 == argc)
			usage();
		/* these options take one argument */
		else if (!strcmp(argv[i], "-l"))   /* number of lines in vertical list */
			lines = atoi(argv[++i]);
		else if (!strcmp(argv[i], "-t"))   /* truncate items to N characters */
			truncate_len = atoi(argv[++i]);
		else if (!strcmp(argv[i], "-m"))
			mon = atoi(argv[++i]);
		else if (!strcmp(argv[i], "-p"))   /* adds prompt to left of input field */
			prompt = argv[++i];
		else if (!strcmp(argv[i], "-S"))   /* suffix hint after input text */
			suffix = argv[++i];
		else if (!strcmp(argv[i], "-fn"))  /* font or font set */
			fonts[0] = argv[++i];
		else if (!strcmp(argv[i], "-nb"))  /* normal background color */
			colors[SchemeNorm][ColBg] = argv[++i];
		else if (!strcmp(argv[i], "-nf"))  /* normal foreground color */
			colors[SchemeNorm][ColFg] = argv[++i];
		else if (!strcmp(argv[i], "-sb"))  /* selected background color */
			colors[SchemeSel][ColBg] = argv[++i];
		else if (!strcmp(argv[i], "-sf"))  /* selected foreground color */
			colors[SchemeSel][ColFg] = argv[++i];
		else if (!strcmp(argv[i], "-w"))   /* embedding window id */
			embed = argv[++i];
		else
			usage();

	if (!setlocale(LC_CTYPE, "") || !XSupportsLocale())
		fputs("warning: no locale support\n", stderr);
	if (!(dpy = XOpenDisplay(NULL)))
		die("cannot open display");
	screen = DefaultScreen(dpy);
	root = RootWindow(dpy, screen);
	if (!embed || !(parentwin = strtol(embed, NULL, 0)))
		parentwin = root;
	if (!XGetWindowAttributes(dpy, parentwin, &wa))
		die("could not get embedding window attributes: 0x%lx",
		    parentwin);
	drw = drw_create(dpy, screen, root, wa.width, wa.height);
	if (!drw_fontset_create(drw, fonts, LENGTH(fonts)))
		die("no fonts could be loaded.");
	lrpad = drw->fonts->h;

#ifdef __OpenBSD__
	if (pledge("stdio rpath", NULL) == -1)
		die("pledge");
#endif

	if (fast && !isatty(0)) {
		grabkeyboard();
		readstdin();
	} else {
		readstdin();
		grabkeyboard();
	}
	setup();
	run();

	return 1; /* unreachable */
}
