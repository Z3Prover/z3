fof(ax1,axiom, lives(agatha)).
fof(ax2,axiom, lives(butler)).
fof(ax3,axiom, lives(charles)).

fof(ax4,axiom, ! [X] : (lives(X) => (X = agatha | X = butler | X = charles))).
fof(ax5,axiom, ! [X,Y] : (killed(X,Y) => hates(X,Y))).
fof(ax6,axiom, ! [X,Y] : (killed(X,Y) => ~ richer(X,Y))).

fof(ax7,axiom, ! [X] : (hates(agatha,X) => ~ hates(charles,X))).
fof(ax8,axiom, ! [X] : (X != butler => hates(agatha,X))).
fof(ax9,axiom, ! [X] : (~ richer(X,agatha) => hates(butler,X))).
fof(ax10,axiom, ! [X] : (hates(agatha,X) => hates(butler,X))).
fof(ax11,axiom, ! [X] : (? [Y] : ~ hates(X,Y))).

fof(ax12,axiom, agatha != butler).
fof(ax13,axiom, ? [X] : killed(X,agatha)).

fof(conj,conjecture, killed(agatha,agatha)).

