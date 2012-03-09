" Vim syntax file
" Language:			Sequent
" Maintainer:		Luke Palmer <lrpalmer@gmail.com>
" Last Change:		2021 Mar 9
" Original Author:	Luke Palmer <lrpalmer@gmail.com>

if exists("b:current_syntax") 
    finish 
endif

syn match seqLabel "\(\<[A-Za-z_]\+\)\:"
syn match seqOperator "->"
syn match seqBinding "\<[A-Za-z_]\+\>\(\([^:]\|$\)\&\)"

syn region seqSkolem matchgroup=seqLabel start="\([A-Za-z_]\+\)(" skip=")\.\([A-Za-z_]\+\)(" end=")\(\.[A-Za-z_]\+\)\?" contains=seqExpr

syn region seqDoc start="\[" end="\]" contains=seqDocExpr
syn region seqDocExpr contained matchgroup=seqOperator start="'" end=" \|\]\&" contains=seqSkolem

hi link seqLabel Label
hi link seqOperator Operator
hi link seqDoc   Comment
hi link seqBinding Type
