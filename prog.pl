% 8-queen

q8:-put([1,2,3,4,5,6,7,8],[],X),write(X),nl.
q4:-put([1,2,3,4],[],X),write(X),nl.

aq8:-put([1,2,3,4,5,6,7,8],[],X),write(X),nl,fail.
aq4:-put([1,2,3,4],[],X),write(X),nl,fail.

put([],X,X).
put(Qs,B,Q):-select(Qs,Q1,R),not-take(B,Q1),put(R,[Q1|B],Q).

not-take(R,Q):-Qp=Q+1,Qm=Q-1,xtake(R,Qp,Qm).

xtake([],_,_).
xtake([Q|R],Qp,Qm):-Q!=Qp,Q!=Qm,Qpp=Qp+1,Qmm=Qm-1,xtake(R,Qpp,Qmm).

select([X|Y],X,Y).
select([X|A],B,[X|C]):-select(A,B,C).


% famous program in prolog

die(X):-human(X).
human(socrates).
human(platon).

% integer calculation in prolog

fact(0,1):-!.
fact(X,Y):-N1=X-1,fact(N1,B),Y=X*B,write(Y," = ",X," * ",B),nl.

% zegra question

neighbor(L,R,[L,R|_]).
neighbor(L,R,[_|Xs]) :- neighbor(L,R,Xs).
zebra(X) :- eq(Street, [H1,H2,H3]),
            member(house(red,english,_), Street),
            member(house(_,spanish,dog), Street),
            neighbor(house(_,_,cat), house(_,japanese,_), Street),
            neighbor(house(_,_,cat), house(blue,_,_), Street),
            member(house(_,X,zebra),Street),write(Street),nl.

% 家が３軒あります。その３軒の家はそれぞれ赤・青・緑で塗られています。
% そしてその住人は、それぞれ異なる国籍で、それぞれ異なるペットを買っています。
% イギリス人は赤い家に住んでいます。
% スペイン人は犬を飼っています。
% 日本人は、猫を飼っている人の右側に住んでいます。
% 猫を飼っている人は青色の家の左に住んでいます。
% 誰がシマウマを飼っているでしょう？

