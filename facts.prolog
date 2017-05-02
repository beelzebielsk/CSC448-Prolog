% Facts organized by presentation:
% Basic Premsises:
% 1. Each alien is owned by exactly one person.
% 2. Each person owns exactly one alien.
%		- If you're a person, then you own somebody.
% 3. The people are: Andrew, Dudley, Georgina, and Karen.
% 4. The Aliens are: Flubsub, Gribbet, Jarix, and Wattin.
% 5. Each alien has exactly one power.
% 6. Every power is owned by an alien.
% 7. The powers are: bubbles, colors, eyes, and fins.
% The Clues:
% 1. Dudley owns neither Flubsub nor Jarix.
% 2. If an alien is owned by Dudley, then it's power is not fins.
% 3. Andrew does not own Jarix.
% 4. Jarix's power is eyes.
% 5. Karen owns Wattin.
% 6. Whichever alien Andrew owns, it does not have the power of fins.
% 7. Whichever alien Dudley owns, it does not have the power of bubbles.

% NOTES:
% - It seems like the rules defining what is not a person, or alien, or power,
% are not necessary. Only what I say is a person is a person in the first place.
% The strange behavior from prolog came from some poorly designed recursive
% rule somewhere.


% People, and being an owner means being a person.
person(andrew).
person(dudley).
person(georgina).
person(karen).

% Testing if the owns/direct_owns setup is sensitive to
% order of elements. It definitely is.
%alien(flubsub).
%alien(gribbet).
%alien(jarix).
%alien(wattin).

alien(wattin).
alien(jarix).
alien(flubsub).
alien(gribbet).

power(bubbles).
power(colors).
power(eyes).
power(fins).

% Clue 3. karen has wattin.
% I'm including the use of direct_own because I want a
% non-recursive version of the owning predicate. If I put
% everything in the same owning predicate, then I run into loops
% often enough. I will do this problem by addding entries to direct_own.
% Declare that direct_own can be updated during runtime.
:- dynamic(direct_own/2).
direct_own(karen, wattin).
% If X is a person, Y is an alien, and we have another alien, Z, that is
% not Y, and it can be said that X owns Z, then X does not own Y.
owns(X, Y) :- person(X), alien(Y),
	alien(Z), \=(Y,Z), direct_own(X, Z),
	!, fail.
% If someone already owns that alien, you don't.
owns(X, Y) :- person(X), alien(Y), person(Z),
	\=(X,Z), direct_own(Z, Y), !, fail.
owns(X, Y) :- direct_own(X, Y).
owns(X, Y) :- person(X), =(X, dudley), alien(Y),
	( =(Y, flubsub) ; =(Y, jarix) ), !,
	fail.
% Andrew doesn't own Jarix.
owns(X, Y) :- =(X, andrew), =(Y, jarix), fail.
% The ! because you get here just once. You don't keep going here.
%owns(X, Y) :- person(X), alien(Y), !.
%owns(X, Y) :- person(X), alien(Y).
owns(X, Y) :- person(X), alien(Y), asserta(direct_own(X, Y)).

% Tests: the first two fail, as they should by the earlier
%		exception rules. The last one succeeds, meaning that it makes
%		it through the previous exceptions.
% owns(dudley, flubsub).
% owns(andrew, jarix).
% owns(andrew, flubsub).
% owned by a unique person.
%		I'm puting the non-unification first, because that's something that's
%		immediately testable. The original form is basically infinite
%		recursion.
%		At same time, I'm worried that without a meaning for what Z is (a
%		different owner of the same alien), the statement makes no sense.
% owns(X,Y) :- \=(X,Z), owns(Z,Y), !, fail.
% If X already owns some other alien, then fail. One alien per person.
% owns(X,Y) :- \=(Y,Z), owns(X,Z), !, fail.

% Jarix has the eyes power.
has_power(jarix, eyes).
% Dudley's alien doesn't have fins.
has_power(X,Y) :- owns(dudley, X), =(Y, fins), !, fail.
% Andrew's alien doesn't have fins.
has_power(X,Y) :- owns(andrew, X), =(Y, fins), !, fail.
% Dudley's alien doesn't have bubbles.
has_power(X,Y) :- owns(dudley, X), =(Y, bubbles), !, fail.


/*

% Every alien has a power.
has_power(X,_) :- alien(X).

% Every power is posessed by an alien.
has_power(_,X) :- power(X).

/* Stuff I'm not using right now: {{{

% If you're a person or an alien, then encounter the '!' which prevents backtracking with that choice, and lead to a failure.
%power(X) :- (person(X) ; alien(X)), !, fail.
%
% If you're an alien or power, then encounter the '!' which prevents backtracking with that choice, and lead to a failure.
%person(X) :- (alien(X) ; power(X)), !, fail.
%
% if you own an alien, then you're a person
%person(X) :- owns(X,_).

% If you're a person or a power, then encounter the '!' which prevents backtracking with that choice, and lead to a failure.
% The order of the goals is important, here. (person(X) ; power(X)) fails, because if you ask person(some_power), then prolog will first ask if
% some_power  is an alien, which will then lead it to ask if some_power is a person, which will lead it to ask if it's an alien... and so on.
%alien(X) :- (power(X) ; person(X)), !, fail.

These just don't work. Everything basically has a universal quantifier.
So the first one says that if you're a person, you own everything.
The second one says that if you're an alien, you're owned by everything.
The last one says that, if you own something, then owning fails, which is kinda ridiculous
considering that Y and Z could unify to the same thing.
% Every person owns an alien.
% owns(X,_) :- person(X).
% Every alien is owned by a person.
% owns(_,X) :- alien(X).
% To see if person X owns alien Y, check first if person X owns any other alien (if owns(X,Z) unifies to something).
% If so, stick with that choice (!), then fail. Only one person can own an alien.
% owns(X,Y) :- owns(X,Z), !, fail.

% aliens don't own aliens, powers don't own aliens.
% owns(X,_) :- alien(X), fail.
% owns(X,_) :- power(X), fail.
% persons don't get owned, powers don't get owned.
% owns(_,X) :- person(X), fail.
% owns(_,X) :- power(X), fail.
% Dudley owns neither flubsub, nor jarix.
%
}}}

/* Ideas still being worked out: {{{

If I want to do something like "everyone owns no more than one person"
Then I think I need to do the following:

I need to split up 'owns' into 'direct_owns' and 'owns', where 'owns' can be recursive, and 'direct_owns' is not at all recursive. The rule to say "everyone owns one alien" is recursive, because you have to figure out if they own any other aliens.
* }}}
*/

