% Student name: Xueqing Zhai
% Student number: 1006962413
% UTORid: zhaixueq

% This code is provided solely for the personal and private use of students
% taking the CSC485H/2501H course at the University of Toronto. Copying for
% purposes other than this use is expressly prohibited. All forms of
% distribution of this code, including but not limited to public repositories on
% GitHub, GitLab, Bitbucket, or any other online platform, whether as given or
% with any changes, are expressly prohibited.

% Authors: Ken Shi, Jingcheng Niu and Gerald Penn

% All of the files in this directory and all subdirectories are:
% Copyright (c) 2023 University of Toronto
:- ale_flag(pscompiling, _, parse_and_gen).
:- ensure_loaded(csc485).
lan(en).
question(q1).

% Type Feature Structure

% Do not modify lines 25-37.
bot sub [cat, sem, agr, list].
    sem sub [n_sem, v_sem].
        n_sem sub [programmer, goose, fish] intro [quantity:quantity].
        v_sem sub [observe, catch] intro [subj:sem, obj:sem].

    cat sub [nominal, verbal] intro [agr:agr, sem:sem].
        nominal sub [n, np, det, num] intro [sem:n_sem].
        verbal sub [v, vp, s] intro [sem:v_sem, subcat:list].

    quantity sub [one, two, three].

    list sub [e_list, ne_list].
        ne_list intro [hd:bot, tl:list].

    % Define the type `agr` for agreement.

    % Hint: it should look something like this: 
    % agr intro [your_agr_feature_1:your_agr_type_1, ...].
    %     your_agr_type_1 sub [...].
    %     ...

    % === Your Code Here ===
    agr intro [number:number].
      number sub [sing, plural].
    % ======================


% Specifying the semantics for generation.
% Do not modify.
semantics sem1.
sem1(sem:S, S) if true.

% Lexicon

% Hint: Your lexical entries should look something like this: 
% token ---> (type,
%    feature_name_1:feature_type_1,
%    feature_name_2:feature_type_2, ...). 

% === Your Code Here ===
a ---> (det, agr:number:sing, sem:quantity:one).
one ---> (num, agr:number:sing, sem:quantity:one).
two ---> (num, agr:number:plural, sem:quantity:two).
three ---> (num, agr:number:plural, sem:quantity:three).
programmer ---> (n, agr:number:sing, sem:programmer).
programmers ---> (n, agr:number:plural, sem:programmer).
goose ---> (n, agr:number:sing, sem:goose).
geese ---> (n, agr:number:plural, sem:goose).
fish ---> (n, agr:number:sing, sem:fish).
fish ---> (n, agr:number:plural, sem:fish).
observe ---> (v, agr:number:plural, sem:observe, subcat:[(Obj, np), (Subj, np)]).
observes ---> (v, agr:number:sing, sem:observe, subcat:[(Obj, np), (Subj, np)]).
observed ---> (v, agr:number:sing, sem:observe, subcat:[(Obj, np), (Subj, np)]).
observed ---> (v, agr:number:plural, sem:observe, subcat:[(Obj, np), (Subj, np)]).
catch ---> (v, agr:number:plural, sem:catch, subcat:[(Obj, np), (Subj, np)]).
catches ---> (v, agr:number:sing, sem:catch, subcat:[(Obj, np), (Subj, np)]).
caught ---> (v, sem:catch, agr:number:sing, subcat:[(Obj, np), (Subj, np)]).
caught ---> (v, sem:catch, agr:number:plural, subcat:[(Obj, np), (Subj, np)]).
% ======================

% Rules

% Hint: Your rules should look something like this: 

% rule_name rule
% (product_type, feature3:value3) ===>
% cat> (type1, feature1:value1),
% cat> (type2, feature2:value2).

% === Your Code Here ===
npdetn rule
  (np, sem:Sem, agr:Agr, sem:quantity:Qsem) ===> cat> (det, agr:Agr, sem:quantity:Qsem), sem_head> (n, agr:Agr, sem:Sem).

npnumn rule
  (np, sem:Sem, agr:Agr, sem:quantity:Qsem) ===> cat> (num, agr:Agr, sem:quantity:Qsem), sem_head> (n, agr:Agr, sem:Sem).

vpvnp rule
  (vp, sem:Sem, sem:obj:Sem2, agr:Agr, subcat:(Else, [_|_])) ===>
  sem_head> (v, sem:Sem, agr:Agr, subcat:[Obj|Else]),
  cat> (Obj, sem:Sem2).

snpvp rule
  (s, sem:obj:Sem1, sem:subj:Sem2, sem:Vsem, agr:Agr, subcat:([], Else)) ===>
  cat> (Subj, sem:Sem2, agr:Agr),
  sem_head> (vp, sem:obj:Sem1, sem:Vsem, agr:Agr, subcat:[Subj|Else]).
% ======================
