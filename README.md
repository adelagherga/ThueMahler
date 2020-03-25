# Overview #

This is a git repository containing all code pertinent to the Thue Mahler solver. The corresponding remote is the github repository [ThueMahler](https://github.com/adelagherga/ThueMahler). This repository is used only for Code. The subfolder, Data, is a separate git repository with Dropbox as its remote. All changes to Data should be done seperately, following the instructions on Data/README.md.

---
### Usage ###

##### Cloning a repository #####

To clone the repository mounted on github, you can run:
```
git clone "https://github.com/adelagherga/ThueMahler.git"
```

##### Updating a repository #####

After initially cloning the repository, upon startup, update the repository using:
```
git pull origin master
```

After finishing work on a repository, commit and push any changes to the github remote to update the central github repository:

```
git add .
git commit -m "message"
git push origin master
```