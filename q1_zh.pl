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
lan(zh).
question(q1).

% Type Feature Structure

% Do not modify lines 25-39.
bot sub [cat, sem, agr, cl_types, list].
    sem sub [n_sem, v_sem].
        n_sem sub [programmer, goose, fish] intro [quantity:quantity].
        v_sem sub [observe, catch] intro [subj:sem, obj:sem].

    cl_types sub [ge, ming, zhi, tiao].

    cat sub [nominal, verbal] intro [agr:agr, sem:sem].
        nominal sub [n, np, clp, num, cl] intro [sem:n_sem].
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
    agr intro [cls:cls].
        cls sub [cl_types].
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
yi ---> (num, sem:quantity:one).
liang ---> (num, sem:quantity:two).
san ---> (num, sem:quantity:three).
chengxuyuan ---> (n, sem:programmer, agr:cls:ge).
chengxuyuan ---> (n, sem:programmer, agr:cls:ming).
e ---> (n, sem:goose, agr:cls:zhi).
yu ---> (n, sem:fish, agr:cls:zhi).
yu ---> (n, sem:fish, agr:cls:tiao).
guancha ---> (v, sem:observe, subcat:[(Obj, np), (Subj, np)]).
zhuadao ---> (v, sem:catch, subcat:[(Obj, np), (Subj, np)]).
ge ---> (cl, agr:cls:ge).
ming ---> (cl, agr:cls:ming).
zhi ---> (cl, agr:cls:zhi).
tiao ---> (cl, agr:cls:tiao).
% ======================


% Rules

% Hint: Your rules should look something like this: 

% rule_name rule
% (product_type, feature3:value3) ===>
% cat> (type1, feature1:value1),
% cat> (type2, feature2:value2).

% === Your Code Here ===
clpnumcl rule
(clp, agr:Arg, sem:quantity:Sem) ===> cat> (num, sem:quantity:Sem), sem_head> (cl, agr:Arg).

npclpn rule
(np, agr:Arg, sem:quantity:Qsem, sem:Nsem) ===> cat> (clp, agr:Arg, sem:quantity:Qsem), sem_head> (n, sem:Nsem, agr:Arg).

vpvnp rule
  (vp, sem:Sem, sem:obj:Sem2, subcat:(Rest, [_|_])) ===>
  sem_head> (v, sem:Sem, subcat:[Obj|Rest]),
  cat> (Obj, sem:Sem2).
  
snpvp rule
  (s, sem:obj:Sem1, sem:subj:Sem2, sem:Vsem, subcat:([], Rest)) ===>
  cat> (Subj, sem:Sem2),
  sem_head> (vp, sem:obj:Sem1, sem:Vsem, subcat:[Subj|Rest]).
% ======================