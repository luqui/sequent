runtime! syntax/javascript.vim
unlet b:current_syntax

syntax include @Sequent syntax/sequent.vim
syntax region seqSig matchgroup=seqDelim start="^////$" end="^////$" contains=@Sequent

hi link seqDelim Delimiter

