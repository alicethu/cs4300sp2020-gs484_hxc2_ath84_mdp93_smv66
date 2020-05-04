from . import *
from app.irsystem.models.helpers import *
from app.irsystem.models.helpers import NumpyEncoder as NumpyEncoder
from flask import request, jsonify
from sqlalchemy import and_, or_, func
from itertools import combinations
import re
import math
import html
from collections import Counter
from app import db
from app.irsystem.models import Recipe, RecipeSchema

recipe_schema = RecipeSchema(many=True)

# defining allergy to associated foods mapping
allergy_map = {
    "Dairy": ["butter", "Butter", "cheese", "Cheese", "cream", "Cream", 
        "custard", "Custard", "milk", "Milk", "whey", "yogurt", 
        "Yogurt"],
    "Egg": ["egg", "Egg"],
    "Fish": ["albacore", "anchov", "Anchov", "carp", "Carp", 
        "cod", "Cod", "fish", "Fish", "herring", "mackerel", 
        "pollock", "salmon", "Salmon", "sardine", "tilapia", 
        "salmon", "Salmon", "trout", "tuna", "Tuna", "yellowfin", "yellowtail"],
    "Peanut": ["peanut", "Peanut"],
    "Shellfish": ["clam", "Clam", "crab", "Crab", "crawfish", "Crawfish", 
        "crayfish", "lobster", "mussel",  "oyster", "Oyster", "prawn", "scallop", "shrimp", 
        "Shrimp", "squid"],
    "Soybean": ["soy", "Soy", "soybean", "Soybean", "soy bean"],
    "Tree Nut": ["almond", "Almond", "cashew", "Cashew", "chestnut", 
        "Chestnut", "hazelnut", "Hazelnut", "hickory", "macadamia", "pecan", 
        "Pecan", "pine", "Pine", "pistachio", "Pistachio", "walnut", "Walnut"],
    "Wheat": ["wheat", "Wheat"]
}


def tokenize(text):
    """Returns a list of words that make up the text.
        
    We lowercase everything.
    Regex is used to satisfy this function
        
    Params: {text: String}
    Returns: List
    """
    return re.findall('[a-z]+',text.lower())


def build_inverted_index(rcps,field):
    """ Builds an inverted index from the recipe field.
    Field can be "title", "desc", "categories", "ingredients", or
    "directions", "meal_type".
    Arguments
    =========
    rcps: list of dicts.
    field: a key in the dicts.
    Returns
    =======
    inverted_index: dict
        For each term, the index contains 
        a sorted list of tuples (doc_id, count_of_term_in_doc)
        such that tuples with smaller doc_ids appear first:
        inverted_index[term] = [(d1, tf1), (d2, tf2), ...]
    """
    bofw = set()
    # handling set case of meal_type
    if field == "meal_type":
        bofw = {"breakfast", "lunch", "dinner"}
    else:
        for rec in rcps:
            if rec:
                if rec[field] is not None:
                    words = tokenize(rec[field])
                    for w in words:
                        bofw.add(w)
    
    # initialize inverted index
    inverted_index = dict.fromkeys(bofw,list())
    for k, _ in inverted_index.items():
        inverted_index[k] = list()

    # build inverted index
    for d_id, recipe in enumerate(rcps):
        if recipe[field] is not None:
            words = tokenize(recipe[field])
            for w in set(words):
                inverted_index[w].append((d_id, words.count(w)))
    return inverted_index


def combine_AND_boolean_terms(terms, inverted_index):
    """ Returns the recipe ids that contain 
        all the words in terms.
    """
    if len(terms) == 0:
        return []
    term_to_postings = {}
    for term in terms:
        if term in inverted_index:
            term_l = term.lower()
            term_to_postings[term_l] = [tup[0] for tup in inverted_index[term]]
    
    if len(term_to_postings) == 0:
        return []
    # most efficient run-time, order by number of postings ascending
    terms_in_order = [k for k in sorted(term_to_postings, key=lambda k: len(term_to_postings[k]), reverse=False)] 
    postings = term_to_postings[terms_in_order[0]]
    for i in range(1, len(terms_in_order)):
        postings = merge_postings_ANDAND(postings,term_to_postings[terms_in_order[i]])
    return postings


def combine_NOT_boolean_terms(terms_not,inverted_index):
    """ Returns the recipe ids that contain any of the words in terms.
    """
    if len(terms_not) == 0:
        return []
    term_to_postings = {}
    for term in terms_not:
        if term in inverted_index:
            term_l = term.lower()
            term_to_postings[term_l] = [tup[0] for tup in inverted_index[term]]
    
    if len(term_to_postings) == 0:
        return []
    # most efficient run-time, order by largest document id, ascending
    terms_in_order = [k for k in sorted(term_to_postings, key=lambda k: max(term_to_postings[k]), reverse=False) ]
    postings = term_to_postings[terms_in_order[0]]
    for i in range(1, len(terms_in_order)):
        postings = merge_postings_OROR(postings,term_to_postings[terms_in_order[i]])
    return postings


def merge_postings_ANDAND(postings1, postings2):
    """ Returns the documents in postings1 and postings2.
    """
    merged_postings = [p for p in postings1 if p in postings2]
    return merged_postings


def merge_postings_OROR(postings1, postings2):
    """ Returns the documents in postings1 or postings2.
    """
    merged_postings = postings1
    for p in postings2:
        if p not in merged_postings:
            merged_postings.append(p)
    return sorted(merged_postings)


def merge_postings_ANDNOT(postings1, postings2):
    """ Returns the documents in postings1 and not in postings2.
        
    """
    merged_postings = [p for p in postings1 if p not in postings2]
    return merged_postings


def rank_recipes_boolean(fav_foods,omit_foods,inv_idx,rcps):
    """ Returns the matching recipes in order of best rating

        Params: {fav_foods: List of str
                omit_foods: List of str
                inv_idx: List of tuples
                rcps: List of Dicts
                }

        Returns: recipes: List of Dicts
    """
    rec_ids = merge_postings_ANDNOT(combine_AND_boolean_terms(fav_foods,inv_idx), combine_NOT_boolean_terms(omit_foods,inv_idx))
    if len(rec_ids) == 0:
        return []
    recipes = [rcps[i] for i in rec_ids]
    for r in recipes:
        if r['rating'] is None or r['rating'] > 5:
            r['rating'] = 0
    recipes = sorted(recipes, key=lambda k: k['rating'], reverse=True)
    return recipes


def combine_rank_recipes_ORAND(or_results,fav_foods):
    """ Returns the matching recipes in order of best match
        Params: {fav_foods: List of str
                 or_results: List of Dicts
                }
        Returns: recipes: List of Dicts
    """
    ranked_rcps = []
    
    for r in or_results:
        if r['rating'] is None or r['rating'] > 5:
            r['rating'] = 0
        r['count_matches_title'] = len([food for food in fav_foods if food in tokenize(r['title']) ] )
        r['count_matches_ingr'] = len([food for food in fav_foods if food in tokenize(r['ingredients']) ] )
        r['count_matches_both'] = len([food for food in fav_foods if food in tokenize(r['title']) and food in tokenize(r['ingredients']) ] )
    
    ranked_rcps = sorted(or_results, key=lambda k: (k['rating']/10 + 
        k['count_matches_title']/2 + k['count_matches_ingr']/4 + 
        k['count_matches_both']), reverse=True)
    return ranked_rcps


project_name = "Fitness Dream Team"
net_ids = "Henri Clarke: hxc2, Alice Hu: ath84, Michael Pinelis: mdp93, Genghis Shyy: gs484, Sam Vacura: smv66"

def version_1_search(query, output_message, data):
    if query:
        query = query.lower()
        query_words = query.split(",")
        query_words = [word.strip() for word in query_words]
        if len(query_words) == 1:
            query_words = query_words[0].split(";")
        recipes = Recipe.query.filter(
            or_(
                or_(Recipe.title.like("%{}%".format(word)) for word in query_words),
                or_(Recipe.description.like("%{}%".format(word)) for word in query_words),
                or_(Recipe.ingredients.like("%{}%".format(word)) for word in query_words),
                or_(Recipe.directions.like("%{}%".format(word)) for word in query_words)
            )
        ).all()
        if not recipes:
            output_message = "No Results Found :("
            data = []
        else:
            recipes_out = recipe_schema.dump(recipes)
            inv_idx_ingredients = build_inverted_index(recipes_out, "ingredients")

            # hardcoding []; will replace after input for "foods to omit" is added
            ranked_results = rank_recipes_boolean(query_words, [], inv_idx_ingredients, recipes_out)
            if len(ranked_results) == 0:
                output_message = "No Results Found :(("
                data = []
            else:
                output_message = "Your search: " + query
                data = ranked_results[:10]
    return output_message, data


def version_2_search_helper(query_words, omit_words, recipes):
    all_data = []
    if not recipes:
        all_data = []
        """
        # cosine similarity 
        recipes_out = recipe_schema.dump(Recipe.query.all())
        num_recipes = len(recipes_out)
        inv_idx_ingredients = build_inverted_index(recipes_out, "ingredients")
        idf_dict = compute_idf(inv_idx_ingredients, num_recipes, 0.1, 0.9)
        norms = compute_norms(idf_dict, inv_idx_ingredients, num_recipes)
        ranked_results = cosine_sim(query_words, inv_idx_ingredients, norms, idf_dict, recipes_out)
        if len(ranked_results) == 0:
            all_data = []
        else:
            all_data = ranked_results
        """
    else:
        # boolean search
        recipes_out = recipe_schema.dump(recipes)
        inv_idx_ingredients = build_inverted_index(recipes_out, "ingredients")
        inv_idx_title = build_inverted_index(recipes_out, "title")
        ranked_results = rank_recipes_boolean(query_words, omit_words, inv_idx_ingredients, recipes_out)
        if len(ranked_results) == 0:
            ranked_results = rank_recipes_boolean(query_words, omit_words, inv_idx_title, recipes_out)
            if len(ranked_results) == 0:
                all_data = []
            else:
                all_data = ranked_results[:10]
        else:
            all_data = ranked_results[:10]
    return all_data


def version_2_search(fav_foods, omit_foods, breakfast_selected, lunch_selected, 
    dinner_selected, drink_included):
    # default initializations
    output_message = ''
    breakfast_data = None
    lunch_data = None
    dinner_data = None
    cal_limit = request.args.get('cal-limit')
    if not cal_limit:
        cal_limit = db.session.query(func.max(Recipe.calories)).one()

    if fav_foods:
        output_message = "Your search: " + fav_foods

        # basic query cleaning/splitting 
        # (TODO: data validation to check SQL injection and possibly input type)
        fav_foods = fav_foods.lower()
        query_words = fav_foods.split(",") # accounting for comma-separated queries
        query_words = [word.strip() for word in query_words]
        if len(query_words) == 1:
            query_words = query_words[0].split(";") # accounting for semicolon-separated queries
        
        omit_words = omit_foods.split(",") # accounting for comma-separated queries
        omit_words = [word.strip() for word in omit_words]
        if len(omit_words) == 1:
            omit_words = omit_words[0].split(";") # accounting for semicolon-separated queries

        if breakfast_selected is None and lunch_selected is None and dinner_selected is None:
            breakfast_selected = "on"
            lunch_selected = "on"
            dinner_selected = "on"
        if breakfast_selected:
            breakfast_recipes = None # placeholder initialization
            if drink_included:
                breakfast_recipes = Recipe.query.filter(
                    or_(
                        or_(Recipe.title.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.description.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.ingredients.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.directions.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.categories.like("%{}%".format(word)) for word in query_words),
                    )
                ).filter_by(calories<cal_limit).filter_by(meal_type="breakfast").all()
            else:
                breakfast_recipes = Recipe.query.filter(
                    or_(
                        or_(Recipe.title.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.description.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.ingredients.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.directions.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.categories.like("%{}%".format(word)) for word in query_words),
                    )
                ).filter(Recipe.calories < cal_limit).filter(~Recipe.categories.like("%Drink%")).filter_by(meal_type="breakfast").all()
            breakfast_data = version_2_search_helper(query_words, omit_words, breakfast_recipes)
        if lunch_selected:
            lunch_recipes = None # placeholder initialization
            if drink_included:
                lunch_recipes = Recipe.query.filter(
                    or_(
                        or_(Recipe.title.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.description.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.ingredients.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.directions.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.categories.like("%{}%".format(word)) for word in query_words),
                    )
                ).filter_by(meal_type="lunch").all()
            else:
                lunch_recipes = Recipe.query.filter(
                    or_(
                        or_(Recipe.title.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.description.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.ingredients.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.directions.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.categories.like("%{}%".format(word)) for word in query_words),
                    )
                ).filter(~Recipe.categories.like("%Drink%")).filter_by(meal_type="lunch").all()
            lunch_data = version_2_search_helper(query_words, omit_words, lunch_recipes)
        if dinner_selected:
            dinner_recipes = None # placeholder initialization
            if drink_included:
                dinner_recipes = Recipe.query.filter(
                    or_(
                        or_(Recipe.title.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.description.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.ingredients.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.directions.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.categories.like("%{}%".format(word)) for word in query_words),
                    )
                ).filter_by(meal_type="dinner").all()
            else:
                dinner_recipes = Recipe.query.filter(
                    or_(
                        or_(Recipe.title.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.description.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.ingredients.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.directions.like("%{}%".format(word)) for word in query_words),
                        or_(Recipe.categories.like("%{}%".format(word)) for word in query_words),
                    )
                ).filter(~Recipe.categories.like("%Drink%")).filter_by(meal_type="dinner").all()
            dinner_data = version_2_search_helper(query_words, omit_words, dinner_recipes)
        result_success = False
        for data in [breakfast_data, lunch_data, dinner_data]:
            if data is not None and len(data) > 0:
                result_success = True
                break
        if not result_success:
            output_message = "No Results Found:("
    return output_message, breakfast_data, lunch_data, dinner_data


def final_search(query_words, omit_words, recipes_by_title, recipes_by_ingredients):
    all_data = []
    if not recipes_by_title and not recipes_by_ingredients:
        all_data = []
    else:
        # boolean search
        recipes_title_out = recipe_schema.dump(recipes_by_title)
        # inv_idx_ingredients = build_inverted_index(recipes_out, "ingredients")
        # inv_idx_title = build_inverted_index(recipes_out, "title")
        # ranked_results = rank_recipes_boolean(query_words, omit_words, inv_idx_title, recipes_out)
        ranked_results = combine_rank_recipes_ORAND(recipes_title_out, query_words)
        if len(ranked_results) < 10:
            recipes_ingredients_out = recipe_schema.dump(recipes_by_ingredients)
            ranked_ingredient_results = combine_rank_recipes_ORAND(recipes_ingredients_out, query_words)
            if len(ranked_ingredient_results) == 0:
                all_data = []
            else:
                i = 0
                while len(ranked_results) < 10 and i < len(ranked_ingredient_results):
                    ranked_results.append(ranked_ingredient_results[i])
                    i += 1
                all_data = ranked_results
        else:
            all_data = ranked_results[:10]
    return all_data


"""
Returns a list of recipes such that each recipe...
1) is categorized as the specified meal type, m_type;
2) contains (in the field specified by field_name) at least one of the words in 
    query_words_with_caps;
3) contains (in the field specified by field_name) none of the words in
    omit_words_with_caps;
4) has a number of calories less than or equal to cal_limit;
and 5) is not categorized as "Drink" if drink_included is None
"""
def get_recipes_by_OR(m_type, query_words_with_caps, omit_words_with_caps, 
    cal_limit, drink_included, allergy_lst, field_name):
    recipes = None # temporary initialization
    if field_name == "title":
        if drink_included:
            recipes = Recipe.query.filter(
                        and_(
                            or_(Recipe.title.like("%{}%".format(word)) for word in query_words_with_caps),
                            and_(~Recipe.title.like("%{}%".format(word)) for word in omit_words_with_caps),
                            and_(~Recipe.ingredients.like("%{}%".format(word)) for word in allergy_lst)
                        )).filter(Recipe.calories <= cal_limit)\
                            .filter_by(meal_type=m_type).all()
        else:
            recipes = Recipe.query.filter(
                        and_(
                            or_(Recipe.title.like("%{}%".format(word)) for word in query_words_with_caps),
                            and_(~Recipe.title.like("%{}%".format(word)) for word in omit_words_with_caps),
                            and_(~Recipe.ingredients.like("%{}%".format(word)) for word in allergy_lst)
                        )).filter(Recipe.calories <= cal_limit)\
                            .filter(~Recipe.categories.like("%Drink%"))\
                                .filter_by(meal_type=m_type).all()
    if field_name == "ingredients":
        if drink_included:
            recipes = Recipe.query.filter(
                        and_(
                            or_(Recipe.ingredients.like("%{}%".format(word)) for word in query_words_with_caps),
                            and_(~Recipe.ingredients.like("%{}%".format(word)) for word in omit_words_with_caps),
                            and_(~Recipe.ingredients.like("%{}%".format(word)) for word in allergy_lst)
                        )).filter(Recipe.calories <= cal_limit)\
                            .filter_by(meal_type=m_type).all()
        else:
            recipes = Recipe.query.filter(
                        and_(
                            or_(Recipe.ingredients.like("%{}%".format(word)) for word in query_words_with_caps),
                            and_(~Recipe.ingredients.like("%{}%".format(word)) for word in omit_words_with_caps),
                            and_(~Recipe.ingredients.like("%{}%".format(word)) for word in allergy_lst)
                        )).filter(Recipe.calories <= cal_limit)\
                            .filter(~Recipe.categories.like("%Drink%"))\
                                .filter_by(meal_type=m_type).all()
    return recipes


@irsystem.route('/', methods=['GET'])
def search():
    # obtaining query inputs
    query = request.args.get('search') # for version 1 only
    fav_foods = request.args.get('fav-foods')
    omit_foods = request.args.get('res-foods')
    cal_limit = request.args.get('cal-limit')
    version = request.args.get('version')
    breakfast_selected = request.args.get('breakfast')
    lunch_selected = request.args.get('lunch')
    dinner_selected = request.args.get('dinner')
    drink_included = request.args.get('include-drink')
    allergies = request.args.getlist('allergies')

    # user input sanitization
    if version is not None and not version.isnumeric():
        version = None
    if omit_foods:
        omit_foods = html.escape(omit_foods)
    if breakfast_selected:
        breakfast_selected = html.escape(breakfast_selected)
    if lunch_selected:
        lunch_selected = html.escape(lunch_selected)
    if dinner_selected:
        dinner_selected = html.escape(dinner_selected)
    if drink_included:
        drink_included = html.escape(drink_included)
    
    # handling allergy input
    allergy_lst = []
    selected_allergies = []
    if len(allergies) > 0:
        for i in range(len(allergies)):
            current = allergies[i]
            current = html.escape(current)
            if current in allergy_map:
                selected_allergies.append(current)
                allergy_lst += allergy_map[current]
    
    # check if user specifies any meal types or not
    no_meal_type_specified = (breakfast_selected is None 
        and lunch_selected is None and dinner_selected is None)

    # if calorie limit is not provided, the limit is set to maximum number of
    # calories for any recipe in the database, so that all recipes are allowed
    max_calories = int(db.session.query(func.max(Recipe.calories)).one()[0])
    if not cal_limit:
        cal_limit = max_calories

    # default initialization of output
    output_message = ''
    breakfast_data = None
    lunch_data = None
    dinner_data = None

    # rendering template for Prototype 1
    if version is not None and int(version) == 1:
        output_message, data = version_1_search(query, output_message, [])
        return render_template('search-v1.html', name=project_name, netid=net_ids, output_message=output_message, data=data)
    elif version is not None and int(version) == 2:
        output_message, breakfast_data, lunch_data, dinner_data = version_2_search(
            fav_foods, omit_foods, breakfast_selected, lunch_selected, dinner_selected, 
            drink_included)
        return render_template('search-v2.html', name=project_name, 
            netid=net_ids, output_message=output_message, breakfast_data=breakfast_data, 
            lunch_data=lunch_data, dinner_data=dinner_data)
    else:
        if fav_foods:
            fav_foods = html.escape(fav_foods)
            output_message = "Your search: " + fav_foods

            # basic query cleaning/splitting 
            # (TODO: data validation to check SQL injection and possibly input type)
            fav_foods = fav_foods.lower()
            query_words = fav_foods.split(",") # accounting for comma-separated queries
            query_words = [word.strip() for word in query_words]
            if len(query_words) == 1:
                query_words = query_words[0].split(";") # accounting for semicolon-separated queries
            
            # list of query words, both in original form (as input by user) and capitalized
            query_words_with_caps = []
            for word in query_words:
                multi_word_lst = word.split(" ")
                multi_word = "" # placeholder initialization
                if len(multi_word_lst) > 1:
                    for w in multi_word_lst:
                        multi_word += w.capitalize() + " "
                if len(multi_word) > 0:
                    query_words_with_caps.append(multi_word.strip())
                query_words_with_caps.append(word)
                query_words_with_caps.append(word.capitalize())
            
            omit_words_with_caps = []
            omit_words = []
            if omit_foods:
                omit_words = omit_foods.split(",") # accounting for comma-separated queries
                omit_words = [word.strip() for word in omit_words]
                if len(omit_words) == 1:
                    omit_words = omit_words[0].split(";") # accounting for semicolon-separated queries

                for word in omit_words:
                    omit_words_with_caps.append(word)
                    omit_words_with_caps.append(word.capitalize())

            if no_meal_type_specified:
                breakfast_selected = "on"
                lunch_selected = "on"
                dinner_selected = "on"

            if breakfast_selected:
                breakfast_recipes_by_title = get_recipes_by_OR("breakfast",
                    query_words_with_caps, omit_words_with_caps, cal_limit, 
                    drink_included, allergy_lst, "title")
                breakfast_recipes_by_ingredients = get_recipes_by_OR("breakfast",
                    query_words_with_caps, omit_words_with_caps, cal_limit, 
                    drink_included, allergy_lst, "ingredients")
                breakfast_data = final_search(query_words, omit_words, 
                    breakfast_recipes_by_title, breakfast_recipes_by_ingredients)
            if lunch_selected:
                lunch_recipes_by_title = get_recipes_by_OR("lunch",
                    query_words_with_caps, omit_words_with_caps, cal_limit, 
                    drink_included, allergy_lst, "title")
                lunch_recipes_by_ingredients = get_recipes_by_OR("lunch",
                    query_words_with_caps, omit_words_with_caps, cal_limit, 
                    drink_included, allergy_lst, "ingredients")
                lunch_data = final_search(query_words, omit_words, 
                    lunch_recipes_by_title, lunch_recipes_by_ingredients)
            if dinner_selected:
                dinner_recipes_by_title = get_recipes_by_OR("dinner",
                    query_words_with_caps, omit_words_with_caps, cal_limit, 
                    drink_included, allergy_lst, "title")
                dinner_recipes_by_ingredients = get_recipes_by_OR("dinner",
                    query_words_with_caps, omit_words_with_caps, cal_limit, 
                    drink_included, allergy_lst, "ingredients")
                dinner_data = final_search(query_words, omit_words, 
                    dinner_recipes_by_title, dinner_recipes_by_ingredients)
            
            result_success = False
            for data in [breakfast_data, lunch_data, dinner_data]:
                if data is not None and len(data) > 0:
                    result_success = True
                    break
            if not result_success:
                output_message = "No Results Found:("
        inputs = {"fav_foods": fav_foods, "omit_foods": omit_foods, 
            "breakfast_selected": breakfast_selected, "lunch_selected": lunch_selected, 
            "dinner_selected": dinner_selected, "drink_included": drink_included, 
            "cal_limit": cal_limit, "allergies": selected_allergies}
        if cal_limit == max_calories:
            inputs["cal_limit"] = ""
        if no_meal_type_specified:
            inputs["breakfast_selected"] = ""
            inputs["lunch_selected"] = ""
            inputs["dinner_selected"] = ""
        return render_template('search.html', name=project_name, 
            netid=net_ids, output_message=output_message, breakfast_data=breakfast_data, 
            lunch_data=lunch_data, dinner_data=dinner_data, inputs=inputs)
