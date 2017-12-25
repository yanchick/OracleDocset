/*
  Copyright 2014, 2015, Oracle and/or its affiliates. All rights reserved.
  Version: 2015.7.3
*/
var suggestions = null, tabInView, typeInView, searchval, federation_categories, federation_products,
  federation_roles, federation_types, noOfProdToShow = 5, prefinedTypesJS, listOfCategory = new Array(),
  prodList = {}, listOfCategories = new Array(),
  previous_request;
var hostname = document.URL;
hostname = hostname.replace(new RegExp("(.*)/(.*)", "g"), "$1");
hostname = hostname + '/';

var jsJspName = "oracleSearch.jsp";
var jsJspNameCategories = "oracleSearchCategories.jsp";
var jsJspNameProducts = "oracleSearchProducts.jsp";
var jsJspNameResults = "oracleSearchResults.jsp";
var jsJspNameTitles = "oracleSearchTitles.jsp";


function addLoadEvent(func) {
  "use strict";
  var oldOnload = window.onload;
  if (typeof window.onload !== "function") {
    window.onload = func;
  } else {
    window.onload = function () { oldOnload(); func(); };
  }
}



function EncodeEntities(s){
  var j = jQuery;
  return j("<div/>").text(s).html();
}

function DecodeEntities(s){
  var j = jQuery;
  return j("<div/>").html(s).text();
}


/*document.onkeydown = function(evt) {
  evt = evt || window.event;
  if (evt.keyCode == 27) {
  }
};*/

function submitForm(elem) {
  var j = jQuery;
   aggregateSearchCriteria(null);	 
   j('#searchField').autocomplete('close');
	 j('#searchField').removeClass('searchstart');
   if (elem !== null && typeof elem !== 'undefined') {
	   j(elem).submit();
   }
}

function clearValueSelection (elem) {
  if (typeof elem === 'undefined' || elem === null) {
    return;
  }
  elem.value = '';
  return
}


function aggregateSearchCriteria (checkbookElem) {
  var allInputElems, checkboxName, iElem, allRole, allType, allCats, allProds, refToAllCheckbox, checkBoxData = new Array(), allULElems, selectedCategory = null, currentCat;
  federation_categories = '';
  federation_products = '';
  federation_roles = '';
  federation_types = '';
  allInputElems = document.getElementsByTagName('input');
  allULElems = document.getElementsByTagName('ul');
  var aggcats = document.getElementById("selectproduct");
  var aggprods = document.getElementById("productSearch");
  var aggroles = document.getElementById("role-aggregated");
  var aggtypes = document.getElementById("type-aggregated");
  currentCat = document.getElementById("category");
  if (aggprods !== null && typeof aggprods !== 'undefined') { federation_products  = aggprods.value;}
  if (aggcats !== null && typeof aggcats !== 'undefined')   { federation_categories = aggcats.value;
    if (currentCat !== null && typeof currentCat !== 'undefined' && currentCat.innerHTML.toLowerCase().indexOf(aggcats.value.replace("-", " ")) === -1 ) { federation_products = ""; }}

  if (aggroles !== null && typeof aggroles !== 'undefined') { federation_roles = aggroles.value;}
  if (aggtypes !== null && typeof aggtypes !== 'undefined') { federation_types = aggtypes.value;}
}

Object.size = function(obj) {
    var size = 0, key;
    for (key in obj) {
        if (obj.hasOwnProperty(key)) 
          size++;
    }
    return size;
};

function getCategories1() {
    var j = jQuery, searchURL = "";
    function setBase() {
     searchURL = window.location.hostname + "/";
     if (searchURL.indexOf("pdb-stage") !== -1) {
       searchURL = "http://" + searchURL+"oracleSearchCategories.jsp";
     } else {
       searchURL = "//" + searchURL.replace("-stage","") + "apps/search/searchCategories.jsp";
     }
    }
    setBase();
    j.ajax({
      url: searchURL,
      dataType: "json",
      async: false,
      success: function( data) {
        var responseJson = data;
        for(var keyProd in responseJson){
          var thisProdName   = keyProd; // db, cloud etc
          var thisProdValues = responseJson[thisProdName];
          listOfCategories[thisProdName] = thisProdValues;
        }
      }
   });
}

function getCategory() {
    var j = jQuery, searchURL = "";
    function setBase() {
     searchURL = window.location.hostname + "/";
     if (searchURL.indexOf("pdb-stage") !== -1) {
       searchURL = "http://" + searchURL+"oracleSearchCategories.jsp";
     } else {
       searchURL = "//" + searchURL.replace("-stage","") + "apps/search/searchCategories.jsp";
     }
    }
    setBase();
    j.ajax({
      url: searchURL,
      dataType: "json",
      async: false,
      success: function( data) {
        var responseJson = data;
        var count = 0;
        for(var keyProd in responseJson){
          var thisProdName   = keyProd; // db, cloud etc
          var thisProdValues = responseJson[thisProdName];
          listOfCategory[thisProdName] = thisProdValues;
          //count = count + 1;
          //alert ("adding: "+thisProdName+": "+thisProdValues);
        }
      }
   });
}
addLoadEvent(getCategories1);

function onLoadInfo() {
  var j = jQuery, searchURL = "";
  function setBase() {
   searchURL = window.location.hostname + "/";
   if (searchURL.indexOf("pdb-stage") !== -1) {
     searchURL = "http://" + searchURL+"oracleSearchTitles.jsp";
   } else {
     searchURL = "//" + searchURL.replace("-stage","") + "apps/search/searchTitles.jsp";
   }
  }
  setBase();
  aggregateSearchCriteria(null);
  //alert(listOfCategories.length);
  //if (listOfCategories.length === 0) {
    //getCategories1();
  //}
  j( "#searchField" ).change(function() {  aggregateSearchCriteria(null);});
  j( "#selectproduct" ).change(function() {  aggregateSearchCriteria(null);});
  j("#searchField").autocomplete({
        scroll: true,
        highlight: true,
        minLength: 3,
        delay: 500,
        open: function() { aggregateSearchCriteria(null);j('#searchField.ui-menu').width(250)},
        source: function(request, response) {
   		  var $this = j(this);
   		    var countItems = 0, firstPartLength = 0;   
          var $element = j(this.element);
          previous_request = $element.data( "jqXHR" );
          if( previous_request ) {
			      previous_request.abort();
          }
          $element.data( "jqXHR", j.ajax({
            url: searchURL, 
            dataType: "json",
            data: {categories: federation_categories, product: federation_products, roles: federation_roles, types: federation_types, q: request.term},
            success: function( data, textStatus, jqXHR) {
                 response( j.map( data.titles, function( item ) {
                    var formattedLabel, formattedValue, productVal = '', contextVal = '', folderVal = '';
                    countItems++;
                    if (item.listtype && item.listtype !== null && item.listtype.match(/specific/)){
                        formattedLabel = "<span class=\"label\">"+item.label.replace(new RegExp("<em>", 'g'),"<strong>").replace(new RegExp("</em>", 'g'),"</strong>")+"</span>" + "<br /><div class=\"summary\">" + item.value.replace(new RegExp("<em>", 'g'),"<strong>").replace(new RegExp("</em>", 'g'),"</strong>")+"<br /><span class=\"prodname\">["+item.prodname+"]</span>"+"</div>";
                        formattedValue = item.label.replace(new RegExp("<em>", 'g'),"").replace(new RegExp("</em>", 'g'),"");
                        productVal = item.product;
                        contextVal = item.context;
                        folderVal = item.folder;
                    }
                    else {
                        
                        if (item.fuzzy && item.fuzzy !== null && item.fuzzy.length > 0){
                          if (countItems > 1){ 
                            formattedLabel = "<span class=\"label\"></span>" +"<span class=\"prodname-generic\">"+item.label +"</span><br />";
                          }
                          request.term = item.fuzzy;
                        }
                        else {
                          formattedLabel   = "<span class=\"label\"></span>" + "<span class=\"prodname-generic\">"+item.label +"</span><br />";
                        }
                        formattedValue = request.term;
                        productVal = item.product;
                        contextVal = item.context;
                        folderVal = item.folder;
                    }
                    if (item.label && item.label !== null && item.label.match(/EMPTYLINESTART/) && item.value.length < 1){
                      return {
                           label: "<span class=\"label\">Related products for your query: "+request.term.replace(/</,"&lt;").replace(/>/,"&gt;").replace(/'/, "&apos;").replace(/"/, "&quot;") +"</span>",
                          value: 'EMPTYLINESTART',
                          product: '',
                          folder: '',
                          context: ''
                      }
                    }
                    else if (item.label && item.label !== null && item.label.match(/EMPTYLINE/) && item.value.length < 1){
                      return {
                          label: "EMPTYLINE",
                          value: '',
                          product: '',
                          folder: '',
                          context: ''
                      }
                    }
                    else{
                      return {
                          label: formattedLabel,
                          value: formattedValue,
                          product: productVal,
                          context: contextVal,
                          folder: folderVal,
                          link: item.link
                      }
                    }
                 }));
            },
            error: function(jqXHR, textStatus, errorThrown){
            }
          }));
        },
        focus: function() {return false;},        
        select: function( event, ui ) {
          if (typeof ui.item.link !== 'undefined' && ui.item.link !== null && ui.item.link.length > 0 ) {
			 window.location = ui.item.link;
		     return;
		  }

          j("#searchField").val(ui.item.value);
		  submitForm(j("#searchField").parent().parent());
        },
        search: function(event, ui) {
	        j(this).addClass('searchstart');
        },
        complete: function() {
            j(this).removeData('jqXHR');
            j(this).removeClass('searchstart');
            response({});
        },
        open: function(event, ui) {
          j(this).removeClass('searchstart');
          var wid, autov = j("#selectproduct").offset().left;
          if (j("#searchField").offset().left < j("#selectproduct").offset().left) {
            autov = j("#searchField").offset().left;
          }
          if(window.screen.width < 620 || window.innerWidth < 620) {
            if (window.screen.width < 620) {
              wid = (window.screen.width - autov -10) + 'px'; 
            } else {
              wid = (window.innerWidth - autov -10) + 'px'; 
            }
          } else {
            if (window.innerWidth - autov < 610) {
              wid = (window.innerWidth - autov -20) + 'px'; 
            } else {
              wid = "600px";
            }
          }
          j(".ui-autocomplete:visible").css({top:"+=5",width: wid, left:autov+'px'});
        
        }
    })
      .data("uiAutocomplete")._renderItem = function(ul, item) {
        if (item.label === 'EMPTYLINE') {
            return j('<li class="ui-state-disabled">'+"<hr />"+'</li>').appendTo(ul);
        } else if (item.value === 'EMPTYLINESTART') {
            return j('<li class="ui-state-disabled">'+item.label+'</li>').appendTo(ul);
        }
        else {
            return j( "<li></li>" )
               .data( "ui-autocomplete-item", item)
               .append( "<a>" + item.label + "</a>" )
               .appendTo( ul );
        }
    };
    
    j("#autocompleteentry").focus(function() {
       j(this).animate({width: '300px', height: '70px'});
    });
    j("#autocompleteentry").blur(function() {
       
    });
    /*j("#searchField").keypress(function(e){ 
    if (!e) e = window.event;   
    if (e.keyCode == '13'){
	  j('#searchField').autocomplete('close');
      return false;
    }
  });*/
  j(window).resize(function() {
    j('#searchField').autocomplete('close');
  });
  j('#searchpage').submit(function() {
    var aggCats, currentCat, prodS;
    aggcats = document.getElementById("selectproduct")
    prodS = document.getElementById("productSearch");
    currentCat = document.getElementById("category");
    if (aggcats !== null && typeof aggcats !== 'undefined')   {
      if (currentCat !== null && typeof currentCat !== 'undefined' && currentCat.innerHTML.toLowerCase().replace(" ", "").trim().indexOf(aggcats.value.toLowerCase()) === -1 ) { if (prodS !== null && typeof prodS !== 'undefined') {prodS.value = ""; } }}  
    });
}
addLoadEvent(onLoadInfo);
function checkText(clearable) {
  "use strict";
  if (clearable !== null) {
    if (clearable.value === 'Search products') { 
      onLoadInfo();
      clearable.value = ''; 
      clearable.style.color = "black";
    } else {
      aggregateSearchCriteria(null);
      onLoadInfo();
    }
  }
}
function addText(clearable) {
  "use strict";
  if (clearable !== null) {
    if (clearable.value.length === 0 || clearable.value === '') {
      onLoadInfo();
      clearable.className = clearable.className.replace("searchstart", "");
      clearable.value = 'Search products'; 
      clearable.style.color = "#999";
    } else {
      aggregateSearchCriteria(null);
      onLoadInfo();
    }
  }
}

