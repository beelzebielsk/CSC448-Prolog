/* Facts: {{{ **********************************************
* Facts organized by presentation:
* Basic Premsises:
* 1. Each alien is owned by exactly one person.
* 2. Each person owns exactly one alien.
*		- If you're a person, then you own somebody.
* 3. The people are: Andrew, Dudley, Georgina, and Karen.
* 4. The Aliens are: Flubsub, Gribbet, Jarix, and Wattin.
* 5. Each alien has exactly one power.
* 6. Every power is owned by an alien.
* 7. The powers are: bubbles, colors, eyes, and fins.
* The Clues:
* 1. Dudley owns neither Flubsub nor Jarix.
* 2. If an alien is owned by Dudley, then it's power is not fins.
* 3. Andrew does not own Jarix.
* 4. Jarix's power is eyes.
* 5. Karen could_own Wattin.
* 6. Whichever alien Andrew owns, it does not have the power of fins.
* 7. Whichever alien Dudley owns, it does not have the power of bubbles.
* }}} ******************************************************/
/* Strategies: {{{ *****************************************
* - Consider allowing it to loop through possibilities until it finally
*   gets a good configuration. That's closer to what you actually did.
*   Basically, tell it to try and figure out of someone could_own
*   someone else.  At all times, it should be the case that at least one
*   person can be shown to own only own alien based on the current facts
*   and no other aliens. That's the person that gets added to the
*   database. Every other person for whom it cannot definitively be
*   shown that they own exactly one alien doesn't get processed, though
*   they should somehow get remembered.
* - Teach it a sort of elimination: make a predicate like 'could_own"
*   that figures out whether it would be possible for a person to own an
*   alien.  If it fails for every single other person, and succeeds for
*   you, then by process of elimination, you own that alien.
* }}} *****************************************************/

/* Basic Object Definitions: {{{ ***************************/
% NOTES:
% - It seems like the rules defining what is not a person, or alien, or
% power, are not necessary. Only what I say is a person is a person in the
% first place.  The strange behavior from prolog came from some poorly
% designed recursive rule somewhere.


% People, and being an owner means being a person.
person(andrew).
person(dudley).
person(georgina).
person(karen).

% Testing if the could_own/direct_owns setup is sensitive to
% order of elements. It definitely is.
%alien(flubsub).
%alien(gribbet).
%alien(jarix).
%alien(wattin).

alien(wattin).
alien(jarix).
alien(gribbet).
alien(flubsub).

power(bubbles).
power(colors).
power(eyes).
power(fins).

/* }}} ****************************************************/

/* Ownership: {{{ *****************************************/

% I'm including the use of direct_own because I want a
% non-recursive version of the owning predicate. If I put
% everything in the same owning predicate, then I run into loops
% often enough. I will do this problem by addding entries to direct_own.
% Declare that direct_own can be updated during runtime.

%%%%%%%%%%%%%%%%%%%% direct_own:
% This represents our definitive knowledge of who owns an alien. It is a
% dynamic predicate, so we will add to this list as the program runs.

:- dynamic(direct_own/2).
% Clue 3. karen has wattin.
direct_own(karen, wattin).

%%%%%%%%%%%%%%%%%%%% could_own: 
% This is true whenever a person could *potentially* own an alien. If
% nothing states that the person doesn't own the alien, then this returns
% true.

%%%%%%%%%% Rule 1: 
% - A person cannot own more than one alien.
% - If X is a person, and Y is an alien, and there exists and alien Z
%   such that X owns Z, then X cannot own Y.
% How it works:
% - If it is the case that X is a person, and Y is an alien, and Z is
%   an alien, and Z does not unify with Y, and we know for sure that X
%   owns Z, then X cannot own Y.
% - The rule will backtrack through all possible other aliens, Z, trying
%   to figure out if X owns Z. If it finds that X owns Z, then all
%   choice points are destroyed by !, then we force complete failure
%   of the `could_own` predicate with the `!, fail` goal.
could_own(X, Y) :- person(X), alien(Y),
	alien(Z), \=(Y,Z), direct_own(X, Z),
	!, fail.

%%%%%%%%%% Rule 2:
% - Only one person can own an alien. In other words (more true to the
%   structure of the real rule), it someone else owns this alien for
%   sure, then you don't.
% - If X is a person, and Y is an alien, and there exists a person Z
%   such that Z owns Y, then X cannot own Y.
% How it works:
% - If it is the case that X is a person, and Y is an alien, and Z is
%   also a person, and X does not unify with Z (they are not the same
%   person), and Z owns Y, then the rule fails.
% - Backtrack through all the possible people, Z, that do not unify with
%   X. If any of them definitely own Y, then eliminate all backtracking
%   and fail. X cannot own Y. `could_own(X, Y)` completely fails. If
%   none of the choices for Z directly own Y, then fail the normal way,
%   which allows us to fall through to later definitions of could_own.
could_own(X, Y) :- person(X), alien(Y), person(Z),
	\=(X,Z), direct_own(Z, Y), !, fail.

%%%%%%%%%% Rule 3:
% - If you definitely own the alien, then you could own it.
could_own(X, Y) :- direct_own(X, Y).

%%%%%%%%%% Rule 4:
% - Dudley doesn't have flubsub or jarix.
% - If X is a person, and X is dudley, and Y is an alien, and Y is
%   either flubsub or jarix, then X cannot own Y.
% How it works:
% - If X is a person, and X unifes with dudley, and Y is an alien, and Y
%   unifies with either flubsub or jarix, then fail. X cannnot own Y.
could_own(X, Y) :- person(X), =(X, dudley), alien(Y),
	( =(Y, flubsub) ; =(Y, jarix) ), !,
	fail.

%%%%%%%%%% Rule 5:
% - Andrew doesn't own jarix.
% How it works:
% - If X unifies with andrew and Y unifies with jarix, then just fail
%   completely.
could_own(X, Y) :- =(X, andrew), =(Y, jarix), !, fail.

%%%%%%%%%% Rule 6:
% - If the search has proceeded to this point, then it has not totally
%   failed in any of the previous rules, so none of them hit the goal
%   (!, fail). At this point, nothing explictly says that X cannot own
%   Y. So, so long as X is a person, and Y is an alien, then X could
%   potentially own Y.
could_own(X, Y) :- person(X), alien(Y).
%owns(X,Y) :- direct_own(X,Y).

%%%%%%%%%%%%%%%%%%%% owns:
% This goes about trying to figure out which people *definitely own*
% which aliens. If it finds that someone defnitely owns an alien, then
% it adds them to the list of known cases by asserting direct_own(X,Y).

%%%%%%%%%% Rule 1:
% - If X could own Y, and no other person could own Y, then X owns Y.
% - If X is a person, and Y is an alien, and X could own Y, then if
%   there exists another person, Z, that could potentially own Y, then X
%   does not definitively own Y. Otherwise, X definitively owns Y, and
%   we add that fact to the knowledge base.
% How it works:
% - If X is a person, and Y is an alien, and X could own Y then do the
%   following:
%		- Look through all people, Z, where Z does not unify with X (Z is a
%		   different person), and check of Z could also own Y. If Z could
%		   own Y, then eliminate all possible backtracking and fail.  X does
%		   not definitively own Y.
%		- If Z does not satisfy this, then backtrack to another Z, and keep
%		   trying until a Z is found that could own Y, or there are no
%		   further choices.
%		- If there are no further choices, the first clause of the `;`
%		   fails normally, while still allowing backtracking. The next
%		   choice point is the choice point provided by `;`, so the next
%		   goal to be executed is the assertion. Since X could own Y and no
%		   other person was found that could own Y, X must own Y, and so we
%		   add that fact to our knowledge base.
% NOTE: For this to be useful, one has to make the query:
% person(X), alien(Y), owns(X,Y).
% This is because the (!, fail) construct will stop all backtracking in
% the current predicate. Thus, there have to be choice points outside of
% the owns(X,Y) predicate that allow the search to continue.
owns(X,Y) :- person(X), alien(Y),
	could_own(X, Y), (
		(person(Z), \=(Z, X), could_own(Z, Y), !, fail) ;
		(asserta(direct_own(X, Y)))
	).

/* }}} ****************************************************/

/* Posession of Powers: {{{ *******************************/

% This is a shameless rip of the ownership section, as the powers have
% just about the same relationship with aliens as aliens do with people.
% The logic is very similar.

:- dynamic(direct_power/2).
% Jarix has the eyes power.
direct_power(jarix, eyes).

could_have_power(X, Y) :- alien(X), power(Y),
	power(Z), \=(Y,Z), direct_power(X, Z),
	!, fail.

could_have_power(X, Y) :- alien(X), power(Y), alien(Z),
	\=(X,Z), direct_power(Z, Y), !, fail.

could_have_power(X, Y) :- direct_power(X, Y).

% Dudley's alien doesn't have fins.
could_have_power(X,Y) :- alien(X), power(Y),
	direct_own(dudley, X), =(Y, fins), !, fail.
% Dudley's alien doesn't have bubbles.
could_have_power(X,Y) :- alien(X), power(Y),
	direct_own(dudley, X), =(Y, bubbles), !, fail.
% Andrew's alien doesn't have fins.
could_have_power(X,Y) :- alien(X), power(Y),
	direct_own(andrew, X), =(Y, fins), !, fail.

could_have_power(X, Y) :- alien(X), power(Y).

has_power(X, Y) :- alien(X), power(Y),
	could_have_power(X, Y), (
		(alien(Z), \=(Z,X), could_have_power(Z, Y), !, fail) ;
		( asserta(direct_power(X,Y)) )
	).

/* }}} ****************************************************/
